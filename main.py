# -*- coding: utf-8 -*-
"""
AutoPrint Cloud 백엔드 서버
----------------------------------------------------------
휴대폰 앱(발신) <-> 이 서버 <-> 프린터가 연결된 PC(수신 프로그램) 를
이어주는 아주 단순한 중계 서버입니다.

동작 방식 (전부 "등록 코드" 하나로 연결됩니다):

  1. 프린터가 연결된 PC에서 receiver_cloud.py 를 처음 실행하면,
     이 서버에 POST /api/register 를 호출해서 6자리 "등록 코드"를
     하나 발급받습니다. (예: 7KX9QM)
  2. PC 사용자는 그 코드를 휴대폰 앱에 입력해둡니다. (최초 1회)
  3. 휴대폰 앱에서 사진/PDF를 고르고 "인쇄 보내기"를 누르면,
     앱이 이 서버의 POST /api/upload/{code} 로 파일을 올립니다.
  4. PC의 receiver_cloud.py 는 몇 초마다 GET /api/poll/{code} 로
     "나한테 온 새 작업 있어?"라고 물어보고, 있으면 파일을 받아
     (GET /api/download/{job_id}) 프린터로 인쇄한 뒤,
     POST /api/ack/{job_id} 로 "처리 완료"를 알립니다.

Gmail API / 구글 로그인을 전혀 사용하지 않습니다. 그래서 구글의
"제한된 범위(restricted scope)" 보안 심사(CASA)를 받을 필요가 없고,
구글 플레이에 자유롭게 앱을 낼 수 있습니다.

실행 방법 (로컬 테스트):
    pip install -r requirements.txt
    uvicorn main:app --host 0.0.0.0 --port 8000

실제 배포는 README_배포방법.txt 를 참고하세요.
"""

import os
import re
import time
import uuid
import sqlite3
import secrets
import string
import shutil
from contextlib import contextmanager
from datetime import datetime, timezone

from fastapi import FastAPI, UploadFile, File, HTTPException, Request
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import FileResponse, JSONResponse

# =========================================================
#  설정
# =========================================================
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.environ.get("AUTOPRINT_DATA_DIR", os.path.join(BASE_DIR, "data"))
UPLOAD_DIR = os.path.join(DATA_DIR, "uploads")
DB_PATH = os.path.join(DATA_DIR, "autoprint.db")

os.makedirs(UPLOAD_DIR, exist_ok=True)

CODE_CHARS = "23456789ABCDEFGHJKLMNPQRSTUVWXYZ"  # 0,O,1,I 처럼 헷갈리는 글자는 뺐습니다
CODE_LENGTH = 6

MAX_FILE_SIZE = 25 * 1024 * 1024  # 25MB
ALLOWED_EXTENSIONS = {".jpg", ".jpeg", ".png", ".gif", ".bmp", ".tif", ".tiff", ".pdf", ".heic", ".heif"}

# 이 시간(초)보다 오래된 완료 작업/파일은 자동으로 청소합니다.
JOB_RETENTION_SECONDS = 24 * 60 * 60  # 24시간
# 이 시간(초)보다 오래 poll이 없었던 프린터 등록은 목록 조회시 만료 표시(삭제는 안 함)
PRINTER_STALE_SECONDS = 90 * 24 * 60 * 60  # 90일

app = FastAPI(title="AutoPrint Cloud", version="1.0.0")

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_methods=["*"],
    allow_headers=["*"],
)


# =========================================================
#  DB
# =========================================================

def _init_db():
    with _db() as con:
        con.execute(
            """
            CREATE TABLE IF NOT EXISTS printers (
                code TEXT PRIMARY KEY,
                created_at TEXT NOT NULL,
                last_seen TEXT
            )
            """
        )
        con.execute(
            """
            CREATE TABLE IF NOT EXISTS jobs (
                id TEXT PRIMARY KEY,
                code TEXT NOT NULL,
                filename TEXT NOT NULL,
                stored_path TEXT NOT NULL,
                status TEXT NOT NULL DEFAULT 'pending',
                created_at TEXT NOT NULL,
                acked_at TEXT
            )
            """
        )
        con.commit()


@contextmanager
def _db():
    con = sqlite3.connect(DB_PATH)
    con.row_factory = sqlite3.Row
    try:
        yield con
    finally:
        con.close()


def _now_iso():
    return datetime.now(timezone.utc).isoformat()


@app.on_event("startup")
def on_startup():
    _init_db()


# =========================================================
#  도우미 함수
# =========================================================

def generate_code(con) -> str:
    for _ in range(50):
        code = "".join(secrets.choice(CODE_CHARS) for _ in range(CODE_LENGTH))
        exists = con.execute("SELECT 1 FROM printers WHERE code = ?", (code,)).fetchone()
        if not exists:
            return code
    raise HTTPException(status_code=500, detail="코드 생성에 실패했습니다. 잠시 후 다시 시도해주세요.")


def normalize_code(code: str) -> str:
    return re.sub(r"[^A-Z0-9]", "", (code or "").upper())


def safe_filename(raw_name: str) -> str:
    raw_name = os.path.basename(raw_name or "photo")
    keep = "".join(c for c in raw_name if c.isalnum() or c in "._- ")
    keep = keep.strip() or "photo"
    return keep[:150]


def ensure_printer_exists(con, code: str):
    row = con.execute("SELECT * FROM printers WHERE code = ?", (code,)).fetchone()
    if not row:
        raise HTTPException(status_code=404, detail="등록되지 않은 코드입니다. 코드를 다시 확인해주세요.")
    return row


def cleanup_old_jobs():
    """완료된 지 오래된 작업의 파일과 DB 기록을 정리한다."""
    cutoff = time.time() - JOB_RETENTION_SECONDS
    with _db() as con:
        rows = con.execute(
            "SELECT id, stored_path FROM jobs WHERE status = 'done'"
        ).fetchall()
        for row in rows:
            try:
                mtime = os.path.getmtime(row["stored_path"]) if os.path.exists(row["stored_path"]) else 0
            except OSError:
                mtime = 0
            if mtime and mtime < cutoff:
                try:
                    if os.path.exists(row["stored_path"]):
                        os.remove(row["stored_path"])
                except OSError:
                    pass
                con.execute("DELETE FROM jobs WHERE id = ?", (row["id"],))
        con.commit()


# =========================================================
#  API
# =========================================================

@app.get("/api/health")
def health():
    return {"status": "ok", "time": _now_iso()}


@app.post("/api/register")
def register_printer():
    """프린터(수신 PC)를 새로 등록하고 등록 코드를 발급한다."""
    with _db() as con:
        code = generate_code(con)
        con.execute(
            "INSERT INTO printers (code, created_at, last_seen) VALUES (?, ?, ?)",
            (code, _now_iso(), _now_iso()),
        )
        con.commit()
    return {"code": code}


@app.get("/api/printers/{code}")
def printer_status(code: str):
    """앱에서 코드가 유효한지 미리 확인할 때 사용."""
    code = normalize_code(code)
    with _db() as con:
        row = ensure_printer_exists(con, code)
    return {"code": row["code"], "registered_at": row["created_at"], "last_seen": row["last_seen"]}


@app.post("/api/upload/{code}")
async def upload_file(code: str, file: UploadFile = File(...)):
    """휴대폰 앱이 인쇄할 파일을 올린다."""
    code = normalize_code(code)

    ext = os.path.splitext(file.filename or "")[1].lower()
    if ext not in ALLOWED_EXTENSIONS:
        raise HTTPException(
            status_code=400,
            detail=f"지원하지 않는 파일 형식입니다 ({ext or '없음'}). 사진(jpg/png 등) 또는 PDF만 보낼 수 있습니다.",
        )

    with _db() as con:
        ensure_printer_exists(con, code)

    job_id = uuid.uuid4().hex
    stored_name = f"{job_id}{ext}"
    stored_path = os.path.join(UPLOAD_DIR, stored_name)

    size = 0
    try:
        with open(stored_path, "wb") as out:
            while True:
                chunk = await file.read(1024 * 1024)
                if not chunk:
                    break
                size += len(chunk)
                if size > MAX_FILE_SIZE:
                    raise HTTPException(status_code=413, detail="파일이 너무 큽니다 (최대 25MB).")
                out.write(chunk)
    except HTTPException:
        if os.path.exists(stored_path):
            os.remove(stored_path)
        raise
    except Exception:
        if os.path.exists(stored_path):
            os.remove(stored_path)
        raise HTTPException(status_code=500, detail="업로드 중 오류가 발생했습니다.")

    if size == 0:
        if os.path.exists(stored_path):
            os.remove(stored_path)
        raise HTTPException(status_code=400, detail="빈 파일입니다.")

    with _db() as con:
        con.execute(
            "INSERT INTO jobs (id, code, filename, stored_path, status, created_at) "
            "VALUES (?, ?, ?, ?, 'pending', ?)",
            (job_id, code, safe_filename(file.filename), stored_path, _now_iso()),
        )
        con.commit()

    return {"job_id": job_id, "filename": safe_filename(file.filename), "size": size}


@app.get("/api/poll/{code}")
def poll_jobs(code: str):
    """수신 PC 프로그램이 몇 초마다 호출해서 새 인쇄 작업이 있는지 확인한다."""
    code = normalize_code(code)
    with _db() as con:
        ensure_printer_exists(con, code)
        con.execute(
            "UPDATE printers SET last_seen = ? WHERE code = ?", (_now_iso(), code)
        )
        rows = con.execute(
            "SELECT id, filename, created_at FROM jobs WHERE code = ? AND status = 'pending' "
            "ORDER BY created_at ASC",
            (code,),
        ).fetchall()
        con.commit()

    jobs = [
        {"id": r["id"], "filename": r["filename"], "created_at": r["created_at"]}
        for r in rows
    ]
    return {"jobs": jobs}


@app.get("/api/download/{job_id}")
def download_job(job_id: str):
    """수신 PC 프로그램이 실제 파일을 내려받는다."""
    with _db() as con:
        row = con.execute("SELECT * FROM jobs WHERE id = ?", (job_id,)).fetchone()
    if not row:
        raise HTTPException(status_code=404, detail="작업을 찾을 수 없습니다.")
    if not os.path.exists(row["stored_path"]):
        raise HTTPException(status_code=410, detail="파일이 이미 삭제되었습니다.")
    return FileResponse(
        row["stored_path"],
        filename=row["filename"],
        media_type="application/octet-stream",
    )


@app.post("/api/ack/{job_id}")
def ack_job(job_id: str):
    """수신 PC 프로그램이 인쇄를 마친 뒤 '처리 완료'를 알린다. 파일은 즉시 삭제한다."""
    with _db() as con:
        row = con.execute("SELECT * FROM jobs WHERE id = ?", (job_id,)).fetchone()
        if not row:
            raise HTTPException(status_code=404, detail="작업을 찾을 수 없습니다.")
        con.execute(
            "UPDATE jobs SET status = 'done', acked_at = ? WHERE id = ?",
            (_now_iso(), job_id),
        )
        con.commit()

    try:
        if os.path.exists(row["stored_path"]):
            os.remove(row["stored_path"])
    except OSError:
        pass

    return {"status": "ok"}


@app.post("/api/cleanup")
def manual_cleanup():
    """오래된 완료 작업을 정리한다. (배포 환경의 스케줄러가 주기적으로 호출해도 되고,
    안 불러도 새 요청이 올 때마다 자연스럽게 조금씩 청소됩니다.)"""
    cleanup_old_jobs()
    return {"status": "ok"}


@app.middleware("http")
async def opportunistic_cleanup(request: Request, call_next):
    # 매 요청마다 아주 가끔(1/200 확률) 오래된 완료 작업을 청소한다.
    # (전용 스케줄러 없이도 디스크가 계속 쌓이지 않게 하기 위함)
    if secrets.randbelow(200) == 0:
        try:
            cleanup_old_jobs()
        except Exception:
            pass
    response = await call_next(request)
    return response
