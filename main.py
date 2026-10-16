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
     POST /api/ack/{job_id} 로 인쇄 결과(성공/실패)를 알립니다.
  5. 휴대폰 앱은 사진을 올린 뒤 GET /api/status/{job_id} 로 몇 초마다
     "인쇄 결과 나왔어?"라고 물어봐서, 성공/실패를 사용자에게 보여줍니다.

[v1.2 보강 사항]
  - 수신 PC는 "비밀 열쇠(토큰)"를 헤더(X-Printer-Token)로 보냅니다. 한 번 등록되면
    그 열쇠가 없는 사람은 poll/download/ack 를 할 수 없습니다. (옛 버전 수신 프로그램은
    열쇠가 없어도 그대로 동작합니다 - 새 버전이 처음 접속할 때 열쇠가 자동 등록됩니다)
  - 없는 코드를 계속 입력해 보는 행위(코드 대입)는 같은 접속 주소에서 일정 횟수가
    넘으면 잠시 막습니다.
  - 등록/업로드 횟수를 제한하고, 한 코드에 쌓일 수 있는 대기 작업 수를 제한합니다.
  - 24시간이 지나도 인쇄되지 않은 대기 파일은 자동으로 삭제합니다.
  - 90일 넘게 접속이 없는 프린터 등록은 자동으로 삭제합니다.
  - 서버가 수신 PC에게 "다음 확인은 몇 초 뒤에 해"라고 알려줘서, 한가할 때는
    확인 횟수(=서버 비용)를 줄입니다.

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
import hashlib
import hmac
import string
import shutil
import threading
from contextlib import contextmanager
from datetime import datetime, timezone, timedelta
from typing import Optional
from urllib.parse import unquote

from fastapi import FastAPI, UploadFile, File, HTTPException, Request
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import FileResponse, JSONResponse
from pydantic import BaseModel

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

# ---- v1.2 보안/효율 설정 ----
# 같은 접속 주소에서 "없는 코드"를 이 시간 안에 이 횟수 넘게 시도하면 잠시 막는다.
BAD_CODE_LIMIT = 20
BAD_CODE_WINDOW_SECONDS = 10 * 60
# 새 코드 발급(등록): 접속 주소당 1시간에 이 횟수까지
REGISTER_LIMIT = 10
REGISTER_WINDOW_SECONDS = 60 * 60
# 업로드: 접속 주소당 1시간에 이 횟수까지
UPLOAD_LIMIT = 120
UPLOAD_WINDOW_SECONDS = 60 * 60
# 한 코드에 인쇄 대기 중인 작업이 이 개수를 넘으면 새 업로드를 거절
MAX_PENDING_PER_CODE = 20
# 인쇄되지 않고 이 시간이 지난 대기 작업은 자동 삭제
PENDING_EXPIRE_SECONDS = 24 * 60 * 60
# 수신 PC에게 알려줄 "다음 확인까지 대기 시간(초)"
POLL_FAST_SECONDS = 5      # 최근 10분 안에 작업이 있었을 때
POLL_MID_SECONDS = 10      # 최근 1시간 안에 작업이 있었을 때
POLL_SLOW_SECONDS = 15     # 그 외 한가할 때
# last_seen(마지막 접속 시각)은 이 간격보다 자주 DB에 쓰지 않는다 (DB 쓰기 줄이기)
LAST_SEEN_WRITE_INTERVAL = 60
# 자동 청소를 실행하는 최소 간격
CLEANUP_INTERVAL_SECONDS = 10 * 60

app = FastAPI(title="AutoPrint Cloud", version="1.2.0")


class AckBody(BaseModel):
    """수신 PC 프로그램이 인쇄를 마친 뒤 결과를 알릴 때 보내는 내용.
    예전 버전의 수신 프로그램은 이 내용 없이 그냥 호출하기도 하므로,
    전부 기본값을 둬서 하위 호환이 되게 한다."""
    status: str = "success"  # "success" 또는 "failed"
    error_message: Optional[str] = None

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
                error_message TEXT,
                created_at TEXT NOT NULL,
                acked_at TEXT
            )
            """
        )
        # 이미 배포되어 있던 서버라면 jobs 테이블에 error_message 컬럼이
        # 없을 수 있으므로, 없는 경우에만 안전하게 추가해준다.
        cols = {row["name"] for row in con.execute("PRAGMA table_info(jobs)").fetchall()}
        if "error_message" not in cols:
            con.execute("ALTER TABLE jobs ADD COLUMN error_message TEXT")
        # v1.2: 프린터(수신 PC) 비밀 열쇠 해시, 마지막 작업 시각
        pcols = {row["name"] for row in con.execute("PRAGMA table_info(printers)").fetchall()}
        if "token_hash" not in pcols:
            con.execute("ALTER TABLE printers ADD COLUMN token_hash TEXT")
        if "last_job_at" not in pcols:
            con.execute("ALTER TABLE printers ADD COLUMN last_job_at TEXT")
        # v1.6: 수신 PC가 쓰는 프린터 이름 (앱 화면에 보여 주기 위함)
        if "printer_name" not in pcols:
            con.execute("ALTER TABLE printers ADD COLUMN printer_name TEXT")
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


# ---------------------------------------------------------
#  접속 주소 확인 / 횟수 제한 (메모리 방식: 서버가 재시작되면 초기화됨)
# ---------------------------------------------------------
_rate_events = {}  # (버킷이름, 접속주소) -> [시각, 시각, ...]
_rate_lock = threading.Lock()


def client_ip(request: Request) -> str:
    """요청을 보낸 쪽의 접속 주소. 배포 서버(Railway) 앞단이 넣어주는 헤더를 우선 사용한다."""
    ip = request.headers.get("x-real-ip")
    if not ip:
        xff = request.headers.get("x-forwarded-for", "")
        ip = xff.split(",")[0].strip() if xff else ""
    if not ip and request.client:
        ip = request.client.host
    return ip or "unknown"


def _rate_count(bucket: str, key: str, window: float) -> int:
    now = time.time()
    with _rate_lock:
        lst = [t for t in _rate_events.get((bucket, key), []) if now - t < window]
        if lst:
            _rate_events[(bucket, key)] = lst
        else:
            _rate_events.pop((bucket, key), None)
        # 메모리가 무한정 늘지 않게 안전장치
        if len(_rate_events) > 50000:
            _rate_events.clear()
        return len(lst)


def _rate_add(bucket: str, key: str):
    with _rate_lock:
        _rate_events.setdefault((bucket, key), []).append(time.time())


def rate_limited(bucket: str, key: str, limit: int, window: float) -> bool:
    return _rate_count(bucket, key, window) >= limit


_bad_events = {}  # 접속주소 -> [(시각, 시도한 코드), ...]


def _bad_add(ip: str, item: str):
    with _rate_lock:
        _bad_events.setdefault(ip, []).append((time.time(), item))
        if len(_bad_events) > 50000:
            _bad_events.clear()


def _bad_distinct_count(ip: str) -> int:
    """최근 시간 안에 이 접속 주소가 시도한 '서로 다른' 잘못된 코드의 개수.
    (같은 잘못된 코드를 계속 반복해서 묻는 낡은 프로그램은 1개로만 센다.
     코드를 이것저것 바꿔 가며 맞혀 보는 대입 공격만 걸러내기 위함)"""
    now = time.time()
    with _rate_lock:
        lst = [(t, i) for (t, i) in _bad_events.get(ip, []) if now - t < BAD_CODE_WINDOW_SECONDS]
        if lst:
            _bad_events[ip] = lst
        else:
            _bad_events.pop(ip, None)
        return len({i for (_, i) in lst})


def check_not_blocked(request: Request):
    """서로 다른 잘못된 코드를 너무 많이 시도한 접속 주소는 잠시 막는다."""
    if _bad_distinct_count(client_ip(request)) >= BAD_CODE_LIMIT:
        raise HTTPException(
            status_code=429,
            detail="잘못된 코드를 너무 많이 입력했습니다. 10분 뒤에 다시 시도해주세요.",
        )


def ensure_printer_exists(con, code: str, request: Request = None):
    if request is not None:
        check_not_blocked(request)
    row = con.execute("SELECT * FROM printers WHERE code = ?", (code,)).fetchone()
    if not row:
        if request is not None:
            _bad_add(client_ip(request), code)
        raise HTTPException(status_code=404, detail="등록되지 않은 코드입니다. 코드를 다시 확인해주세요.")
    return row


# ---------------------------------------------------------
#  수신 PC 비밀 열쇠(토큰)
# ---------------------------------------------------------
def _hash_token(token: str) -> str:
    return hashlib.sha256(token.encode("utf-8")).hexdigest()


def _valid_token_format(token: str) -> bool:
    return bool(token) and 16 <= len(token) <= 128 and re.fullmatch(r"[A-Za-z0-9_\-]+", token) is not None


def authenticate_printer(con, row, request: Request):
    """수신 PC 전용 요청(poll/download/ack)의 열쇠를 확인한다.

    - 이 프린터에 아직 열쇠가 등록 안 돼 있으면(옛 버전): 그냥 통과.
      단, 요청에 열쇠가 들어 있으면 이 열쇠를 이 프린터의 열쇠로 등록한다. (처음 쓴 사람 우선)
    - 열쇠가 등록돼 있으면: 같은 열쇠를 보내야만 통과, 아니면 401.
    """
    token = (request.headers.get("x-printer-token") or "").strip()
    stored = row["token_hash"]

    if not stored:
        if _valid_token_format(token):
            con.execute(
                "UPDATE printers SET token_hash = ? WHERE code = ? AND token_hash IS NULL",
                (_hash_token(token), row["code"]),
            )
            con.commit()
        return

    if not token or not hmac.compare_digest(_hash_token(token), stored):
        _bad_add(client_ip(request), row["code"])
        raise HTTPException(status_code=401, detail="이 코드의 인증 정보가 맞지 않습니다.")


def _token_matches(row, request: Request) -> bool:
    token = (request.headers.get("x-printer-token") or "").strip()
    stored = row["token_hash"] if row is not None else None
    return bool(stored) and bool(token) and hmac.compare_digest(_hash_token(token), stored)


def ensure_printer_for_pc(con, code: str, request: Request):
    """수신 PC 전용 요청용. 올바른 열쇠를 가진 PC는, 같은 공유기를 쓰는 다른 사람이
    코드를 잘못 입력해서 접속 주소가 잠긴 경우에도 영향을 받지 않는다."""
    row = con.execute("SELECT * FROM printers WHERE code = ?", (code,)).fetchone()
    if row is not None and _token_matches(row, request):
        return row
    return ensure_printer_exists(con, code, request)


def printer_for_job(con, job_row):
    return con.execute("SELECT * FROM printers WHERE code = ?", (job_row["code"],)).fetchone()


# ---------------------------------------------------------
#  자동 청소
# ---------------------------------------------------------
_last_cleanup = 0.0


def _iso_ago(seconds: float) -> str:
    return (datetime.now(timezone.utc) - timedelta(seconds=seconds)).isoformat()


def _remove_file(path):
    try:
        if path and os.path.exists(path):
            os.remove(path)
    except OSError:
        pass


def cleanup_old_jobs():
    """오래된 작업/파일/프린터 등록을 정리한다.

    1) 완료(성공/실패)된 지 24시간 지난 작업 기록 삭제
    2) 인쇄 안 된 채 24시간 지난 대기 작업: 파일 삭제 + '실패(시간 초과)'로 표시
       (휴대폰 앱이 결과를 물어보면 실패로 보이도록 기록은 하루 더 남긴다)
    3) 90일 넘게 접속이 없는 프린터 등록과 그 작업 삭제
    4) DB에 없는 채 이틀 넘게 남은 업로드 파일 삭제
    """
    done_cutoff = _iso_ago(JOB_RETENTION_SECONDS)
    pending_cutoff = _iso_ago(PENDING_EXPIRE_SECONDS)
    stale_printer_cutoff = _iso_ago(PRINTER_STALE_SECONDS)
    now_iso = _now_iso()

    with _db() as con:
        # 1) 오래된 완료 작업
        rows = con.execute(
            "SELECT id, stored_path FROM jobs "
            "WHERE status IN ('success', 'failed', 'done') AND acked_at IS NOT NULL AND acked_at < ?",
            (done_cutoff,),
        ).fetchall()
        for row in rows:
            _remove_file(row["stored_path"])
            con.execute("DELETE FROM jobs WHERE id = ?", (row["id"],))

        # 2) 오래 방치된 대기 작업
        rows = con.execute(
            "SELECT id, stored_path FROM jobs WHERE status = 'pending' AND created_at < ?",
            (pending_cutoff,),
        ).fetchall()
        for row in rows:
            _remove_file(row["stored_path"])
            con.execute(
                "UPDATE jobs SET status = 'failed', error_message = ?, acked_at = ? WHERE id = ?",
                ("24시간 안에 인쇄되지 않아 삭제되었습니다. 프린터 컴퓨터가 켜져 있는지 확인하세요.", now_iso, row["id"]),
            )

        # 3) 오래 접속 없는 프린터
        stale = con.execute(
            "SELECT code FROM printers WHERE COALESCE(last_seen, created_at) < ?",
            (stale_printer_cutoff,),
        ).fetchall()
        for p in stale:
            for j in con.execute("SELECT stored_path FROM jobs WHERE code = ?", (p["code"],)).fetchall():
                _remove_file(j["stored_path"])
            con.execute("DELETE FROM jobs WHERE code = ?", (p["code"],))
            con.execute("DELETE FROM printers WHERE code = ?", (p["code"],))

        con.commit()

        # 4) 주인 없는 파일
        try:
            known = {os.path.basename(r["stored_path"]) for r in con.execute("SELECT stored_path FROM jobs").fetchall()}
            limit = time.time() - 2 * 24 * 60 * 60
            for name in os.listdir(UPLOAD_DIR):
                path = os.path.join(UPLOAD_DIR, name)
                if name not in known and os.path.isfile(path) and os.path.getmtime(path) < limit:
                    _remove_file(path)
        except OSError:
            pass


def maybe_cleanup():
    """마지막 청소 이후 일정 시간이 지났으면 청소한다. (스케줄러 없이도 주기적으로 실행됨)"""
    global _last_cleanup
    now = time.time()
    if now - _last_cleanup < CLEANUP_INTERVAL_SECONDS:
        return
    _last_cleanup = now
    try:
        cleanup_old_jobs()
    except Exception:
        pass


def _parse_iso(value):
    try:
        return datetime.fromisoformat(value)
    except Exception:
        return None


def next_poll_seconds(printer_row) -> int:
    """최근에 인쇄 작업이 있었으면 자주, 한가하면 덜 자주 확인하도록 알려준다."""
    last = _parse_iso(printer_row["last_job_at"]) if printer_row["last_job_at"] else None
    if last is None:
        return POLL_SLOW_SECONDS
    age = (datetime.now(timezone.utc) - last).total_seconds()
    if age < 10 * 60:
        return POLL_FAST_SECONDS
    if age < 60 * 60:
        return POLL_MID_SECONDS
    return POLL_SLOW_SECONDS


# =========================================================
#  API
# =========================================================

@app.get("/api/health")
def health():
    return {"status": "ok", "time": _now_iso()}


@app.post("/api/register")
def register_printer(request: Request):
    """프린터(수신 PC)를 새로 등록하고 등록 코드를 발급한다.
    X-Printer-Token 헤더가 있으면 그 열쇠를 이 코드의 열쇠로 바로 등록한다."""
    ip = client_ip(request)
    if rate_limited("register", ip, REGISTER_LIMIT, REGISTER_WINDOW_SECONDS):
        raise HTTPException(status_code=429, detail="등록 요청이 너무 많습니다. 잠시 후 다시 시도해주세요.")
    _rate_add("register", ip)

    token = (request.headers.get("x-printer-token") or "").strip()
    token_hash = _hash_token(token) if _valid_token_format(token) else None

    with _db() as con:
        code = generate_code(con)
        con.execute(
            "INSERT INTO printers (code, created_at, last_seen, token_hash) VALUES (?, ?, ?, ?)",
            (code, _now_iso(), _now_iso(), token_hash),
        )
        con.commit()
    return {"code": code}


@app.get("/api/printers/{code}")
def printer_status(code: str, request: Request):
    """앱에서 코드가 유효한지 미리 확인할 때 사용."""
    code = normalize_code(code)
    with _db() as con:
        row = ensure_printer_exists(con, code, request)
    seen = _parse_iso(row["last_seen"]) if row["last_seen"] else None
    online = bool(seen) and (datetime.now(timezone.utc) - seen).total_seconds() < 180
    return {
        "code": row["code"],
        "registered_at": row["created_at"],
        "last_seen": row["last_seen"],
        "online": online,
        "printer_name": (row["printer_name"] or "") if "printer_name" in row.keys() else "",
    }


@app.post("/api/upload/{code}")
async def upload_file(code: str, request: Request, file: UploadFile = File(...)):
    """휴대폰 앱이 인쇄할 파일을 올린다."""
    code = normalize_code(code)
    ip = client_ip(request)

    ext = os.path.splitext(file.filename or "")[1].lower()
    if ext not in ALLOWED_EXTENSIONS:
        raise HTTPException(
            status_code=400,
            detail=f"지원하지 않는 파일 형식입니다 ({ext or '없음'}). 사진(jpg/png 등) 또는 PDF만 보낼 수 있습니다.",
        )

    with _db() as con:
        ensure_printer_exists(con, code, request)
        pending = con.execute(
            "SELECT COUNT(*) AS n FROM jobs WHERE code = ? AND status = 'pending'", (code,)
        ).fetchone()["n"]
    if pending >= MAX_PENDING_PER_CODE:
        raise HTTPException(
            status_code=429,
            detail="인쇄 대기 중인 파일이 너무 많습니다. 프린터 컴퓨터가 켜져 있는지 확인하고 잠시 후 다시 보내주세요.",
        )
    if rate_limited("upload", ip, UPLOAD_LIMIT, UPLOAD_WINDOW_SECONDS):
        raise HTTPException(status_code=429, detail="너무 많이 보냈습니다. 잠시 후 다시 시도해주세요.")
    _rate_add("upload", ip)

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

    now_iso = _now_iso()
    with _db() as con:
        con.execute(
            "INSERT INTO jobs (id, code, filename, stored_path, status, created_at) "
            "VALUES (?, ?, ?, ?, 'pending', ?)",
            (job_id, code, safe_filename(file.filename), stored_path, now_iso),
        )
        con.execute("UPDATE printers SET last_job_at = ? WHERE code = ?", (now_iso, code))
        con.commit()

    return {"job_id": job_id, "filename": safe_filename(file.filename), "size": size}


@app.get("/api/poll/{code}")
def poll_jobs(code: str, request: Request):
    """수신 PC 프로그램이 주기적으로 호출해서 새 인쇄 작업이 있는지 확인한다.
    응답의 next_poll_seconds 는 '다음 확인까지 기다릴 시간(초)'이다."""
    code = normalize_code(code)
    with _db() as con:
        row = ensure_printer_for_pc(con, code, request)
        authenticate_printer(con, row, request)

        # last_seen 은 일정 간격 이상 지났을 때만 기록한다 (DB 쓰기 줄이기)
        seen = _parse_iso(row["last_seen"]) if row["last_seen"] else None
        now = datetime.now(timezone.utc)
        if seen is None or (now - seen).total_seconds() >= LAST_SEEN_WRITE_INTERVAL:
            con.execute("UPDATE printers SET last_seen = ? WHERE code = ?", (now.isoformat(), code))

        # 수신 PC 가 보낸 프린터 이름을 저장한다 (한글 이름은 URL 인코딩되어 온다)
        raw_name = request.headers.get("x-printer-name")
        if raw_name:
            try:
                new_name = unquote(raw_name).strip()[:80]
            except Exception:
                new_name = ""
            if new_name and new_name != (row["printer_name"] or ""):
                con.execute("UPDATE printers SET printer_name = ? WHERE code = ?", (new_name, code))

        rows = con.execute(
            "SELECT id, filename, created_at FROM jobs WHERE code = ? AND status = 'pending' "
            "ORDER BY created_at ASC",
            (code,),
        ).fetchall()
        con.commit()
        wait = POLL_FAST_SECONDS if rows else next_poll_seconds(row)

    jobs = [
        {"id": r["id"], "filename": r["filename"], "created_at": r["created_at"]}
        for r in rows
    ]
    return {"jobs": jobs, "next_poll_seconds": wait}


@app.get("/api/download/{job_id}")
def download_job(job_id: str, request: Request):
    """수신 PC 프로그램이 실제 파일을 내려받는다."""
    with _db() as con:
        row = con.execute("SELECT * FROM jobs WHERE id = ?", (job_id,)).fetchone()
        if not row:
            raise HTTPException(status_code=404, detail="작업을 찾을 수 없습니다.")
        printer = printer_for_job(con, row)
        if printer is not None:
            authenticate_printer(con, printer, request)
    if not os.path.exists(row["stored_path"]):
        raise HTTPException(status_code=410, detail="파일이 이미 삭제되었습니다.")
    return FileResponse(
        row["stored_path"],
        filename=row["filename"],
        media_type="application/octet-stream",
    )


@app.post("/api/ack/{job_id}")
def ack_job(job_id: str, request: Request, body: AckBody = AckBody()):
    """수신 PC 프로그램이 인쇄를 마친 뒤 결과(성공/실패)를 알린다. 파일은 즉시 삭제한다."""
    status = "failed" if body.status == "failed" else "success"

    with _db() as con:
        row = con.execute("SELECT * FROM jobs WHERE id = ?", (job_id,)).fetchone()
        if not row:
            raise HTTPException(status_code=404, detail="작업을 찾을 수 없습니다.")
        printer = printer_for_job(con, row)
        if printer is not None:
            authenticate_printer(con, printer, request)
        con.execute(
            "UPDATE jobs SET status = ?, error_message = ?, acked_at = ? WHERE id = ?",
            (status, (body.error_message or None) and body.error_message[:300], _now_iso(), job_id),
        )
        con.commit()

    _remove_file(row["stored_path"])
    return {"status": "ok"}


@app.get("/api/status/{job_id}")
def job_status(job_id: str):
    """휴대폰 앱이 인쇄 결과(성공/실패)를 확인할 때 사용한다.
    아직 인쇄 전이면 status="pending"을 돌려준다."""
    with _db() as con:
        row = con.execute(
            "SELECT status, error_message FROM jobs WHERE id = ?", (job_id,)
        ).fetchone()
    if not row:
        # 오래돼서 이미 정리된 작업일 수 있다 - 이 경우는 이미 성공적으로
        # 끝났다고 보는 것이 안전하다 (실패였다면 정리 전에 앱이 먼저 물어봤을 것).
        return {"status": "success", "error_message": None}
    return {"status": row["status"], "error_message": row["error_message"]}


@app.post("/api/cleanup")
def manual_cleanup():
    """오래된 작업을 정리한다. (스케줄러가 호출해도 되고, 안 불러도 서버가 일정 시간마다 알아서 청소합니다.)"""
    cleanup_old_jobs()
    return {"status": "ok"}


@app.middleware("http")
async def periodic_cleanup(request: Request, call_next):
    # 마지막 청소 후 10분이 지났으면 요청 중에 한 번 청소한다.
    # (전용 스케줄러 없이도 디스크가 계속 쌓이지 않게 하기 위함)
    maybe_cleanup()
    response = await call_next(request)
    return response
