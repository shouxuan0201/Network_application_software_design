#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
bc_selftest.py — 以腳本化的原始 TCP 客戶端驗證 BC/1.0 伺服器行為（協定自我測試工具）。

用法：
  python bc_selftest.py --server "python 你的程式/bc.py server" [--port 5600] [--json 結果.json]

說明：
  1. 受測伺服器必須支援規範第 5.2 節的命令列選項，並依第 5.6 節輸出 JSON Lines 日誌。
  2. 共 48 項檢查，項目名稱固定不變。某一節中途發生例外時，該節尚未執行的項目一律記為失敗，
     總項數仍為 48，因此不同次執行的結果可以逐項比較。
  3. 每次啟動伺服器都改用一個尚未被占用的新埠號，自 --port 起算，約使用 15 個埠號。
  4. 全部檢查約需 3 分鐘；加上 --skip-bots 可略過最花時間的第 [1] 節（10 項記為「略過」）。
"""
import argparse
import asyncio
import glob
import hashlib
import itertools
import json
import os
import random
import secrets
import shlex
import signal
import socket
import sys
import tempfile

# 本工具刻意不匯入參考實作，可單獨發給學生，用來測試任一組的伺服器。
ALL_NUMBERS = ["".join(p) for p in itertools.permutations("0123456789", 4)]
POSIX = os.name == "posix"


def score(guess, secret):
    a = sum(g == s for g, s in zip(guess, secret))
    return a, len(set(guess) & set(secret)) - a


def make_commit(secret, salt):
    return hashlib.sha256(f"{secret}:{salt}".encode("ascii")).hexdigest()


# ---------------------------------------------------------------------------
# 檢查項目登錄：每一節的項目名稱事先固定，未執行到的項目在該節結束時補記為失敗
# ---------------------------------------------------------------------------
LABELS = {}
for _n in range(2, 7):
    LABELS[f"bots{_n}"] = [f"{_n} 人：10 局皆正常結束且恰有一位第一名",
                           f"{_n} 人：所有揭示驗證皆為 OK"]
LABELS["lobby_errors"] = [
    "非 JSON → BAD_JSON（非致命）",
    "HELLO 之前送其他訊息 → UNEXPECTED（致命）",
    "致命錯誤後伺服器關閉連線",
    "主版本不符 → VERSION_UNSUPPORTED",
    "HELLO 缺 kind → BAD_FIELD（致命）",
    "HELLO 空白名稱 → INVALID_VALUE（致命）",
    "單行超過 4096 位元組 → LINE_TOO_LONG",
    "連線後 10 秒未送 HELLO → TIMEOUT",
]
LABELS["game_errors"] = [
    "合法 HELLO → WELCOME",
    "名稱重複 → NAME_TAKEN",
    "人數到齊 → GAME_START 含完整 rules",
    "開局後加入 → GAME_IN_PROGRESS",
    "承諾階段喊數 → UNEXPECTED",
    "承諾值格式錯誤 → INVALID_VALUE",
    "重複 COMMIT → DUPLICATE",
    "COMMITS 廣播所有承諾值",
    "PING → PONG 並回傳 nonce",
    "CHAT 由伺服器轉播",
    "未知類型 → UNKNOWN_TYPE",
    "turn_id 為布林值 → BAD_FIELD",
    "turn_id 不符 → STALE_TURN",
    "數字重複的喊數 → INVALID_VALUE",
    "非喊數者喊數 → NOT_YOUR_TURN",
    "回報 3A1B → INVALID_VALUE",
    "重複回報 → DUPLICATE",
    "錯誤測試後遊戲仍正常結束",
    "誠實玩家揭示驗證 OK",
]
LABELS["liar"] = ["永遠回報 0A0B → 在 TURN_RESULT 的 disqualified 中被取消資格",
                  "被取消資格者在 GAME_OVER 無名次"]
LABELS["liar2"] = ["一致地假裝另一個秘密 → 揭示判定 INCONSISTENT",
                   "一致說謊者終局驗證後取消名次"]
LABELS["badcommit"] = ["揭示的秘密與承諾值不符 → BAD_COMMIT"]
LABELS["quit"] = ["斷線玩家出現在 TURN_RESULT 的 forfeited",
                  "棄權者名次低於所有被猜中者與存活者"]
LABELS["mute"] = ["回報逾時 → 該回合 forfeited"]
LABELS["afk"] = ["連續 2 次逾時未喊數 → 第 2 次跳過時棄權"]
LABELS["nocommit"] = ["承諾逾時 → ERROR TIMEOUT 並移出本局"]
LABELS["abort"] = ["承諾後不足 2 人 → GAME_OVER ABORTED"]
ALL_LABELS = [l for ls in LABELS.values() for l in ls]
assert len(ALL_LABELS) == len(set(ALL_LABELS)) == 48

RESULTS = {}      # label -> (ok, note)
SKIPPED = []


def check(cond, label, note=""):
    """記錄一項檢查；label 必須是 LABELS 中登錄過的固定名稱，變動的資訊放在 note。"""
    assert label in ALL_LABELS, f"未登錄的檢查項目：{label}"
    ok = bool(cond)
    if label in RESULTS:            # 同一項目不重複計分，以第一次的結果為準
        return ok
    RESULTS[label] = (ok, note)
    print(("  [PASS] " if ok else "  [FAIL] ") + label + (f"（{note}）" if note else ""), flush=True)
    return ok


async def run_section(key, title, fn, *args):
    """執行一節測試；中途發生例外時，本節尚未執行的項目記為失敗。"""
    if title:
        print(f"\n{title}", flush=True)
    note = "未執行"
    try:
        await fn(*args)
    except Exception as ex:                                  # noqa: BLE001  測試工具必須能從任何錯誤中恢復
        note = f"本節中途中斷：{type(ex).__name__}: {ex}"[:200]
        print(f"  （{note}）", flush=True)
    for label in LABELS[key]:
        if label not in RESULTS:
            check(False, label, note)


# ---------------------------------------------------------------------------
# 原始 TCP 測試客戶端
# ---------------------------------------------------------------------------
class Raw:
    """直接說協定的測試客戶端。
    recv() 與 expect() 在連線關閉或逾時時都回傳 None（逾時時 timed_out 為 True）；
    expect() 會把不相符的訊息暫存，之後由 recv() 依序取出；closed_within() 只在連線確實被關閉時回傳 True。
    伺服器送來無法解析的行，以 {"type": "__BAD_JSON__", "raw": ...} 表示。"""

    def __init__(self, port, host="127.0.0.1"):
        self.host, self.port = host, port
        self.inbox, self.pending = [], []
        self.r = self.w = None
        self.eof = False
        self.timed_out = False

    async def connect(self):
        self.r, self.w = await asyncio.open_connection(self.host, self.port, limit=1 << 20)

    def send(self, obj):
        data = obj if isinstance(obj, bytes) else (json.dumps(obj, ensure_ascii=False) + "\n").encode()
        try:
            self.w.write(data)
        except (ConnectionError, OSError, RuntimeError, AttributeError):
            pass

    async def _read(self, timeout):
        """讀一則訊息；連線關閉回傳 None；逾時拋出 asyncio.TimeoutError。"""
        if self.eof or self.r is None:
            self.eof = True
            return None
        try:
            raw = await asyncio.wait_for(self.r.readline(), timeout)
        except asyncio.TimeoutError:      # Python 3.11 起 TimeoutError 是 OSError 的子類別，必須先攔下
            raise
        except (ConnectionError, OSError):
            raw = b""
        except ValueError:                                   # 單行超過 1 MiB
            raw = b'{"type": "__BAD_JSON__", "raw": "line too long"}\n'
        if not raw:
            self.eof = True
            return None
        try:
            m = json.loads(raw)
        except ValueError:
            m = None
        if not isinstance(m, dict):
            m = {"type": "__BAD_JSON__", "raw": raw[:200].decode("utf-8", "replace")}
        self.inbox.append(m)
        return m

    async def recv(self, timeout=5.0):
        if self.pending:
            return self.pending.pop(0)
        self.timed_out = False
        try:
            return await self._read(timeout)
        except asyncio.TimeoutError:
            self.timed_out = True
            return None

    async def expect(self, mtype, timeout=5.0):
        for i, m in enumerate(self.pending):
            if m.get("type") == mtype:
                return self.pending.pop(i)
        loop = asyncio.get_running_loop()
        deadline = loop.time() + timeout
        self.timed_out = False
        while True:
            left = deadline - loop.time()
            if left <= 0:
                self.timed_out = True
                return None
            try:
                m = await self._read(left)
            except asyncio.TimeoutError:
                self.timed_out = True
                return None
            if m is None:
                return None
            if m.get("type") == mtype:
                return m
            self.pending.append(m)

    async def closed_within(self, timeout=5.0):
        """timeout 秒內連線是否被對方關閉；期間收到的訊息會暫存。"""
        loop = asyncio.get_running_loop()
        deadline = loop.time() + timeout
        while True:
            if self.eof:
                return True
            left = deadline - loop.time()
            if left <= 0:
                return False
            try:
                m = await self._read(left)
            except asyncio.TimeoutError:
                return False
            if m is None:
                return True
            self.pending.append(m)

    async def hello(self, name, kind="human", protocol="BC/1.0", team="TEST"):
        await self.connect()
        self.send({"type": "HELLO", "protocol": protocol, "name": name, "team": team, "kind": kind})
        return await self.expect("WELCOME")

    def close(self):
        try:
            if self.w is not None:
                self.w.close()
        except Exception:                                    # noqa: BLE001
            pass


def is_err(m, code, fatal=None):
    return isinstance(m, dict) and m.get("type") == "ERROR" and m.get("code") == code \
        and (fatal is None or m.get("fatal") is fatal)


# ---------------------------------------------------------------------------
# 受測伺服器的啟動與結束
# ---------------------------------------------------------------------------
def split_cmd(cmd):
    """把命令字串切成參數；Windows 上保留反斜線並去掉外層引號。"""
    if POSIX:
        return shlex.split(cmd)
    return [t[1:-1] if len(t) >= 2 and t[0] == t[-1] and t[0] in "\"'" else t
            for t in shlex.split(cmd, posix=False)]


def port_is_free(port):
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    try:
        s.bind(("0.0.0.0", port))
        return True
    except OSError:
        return False
    finally:
        s.close()


class Ports:
    """依序配發尚未被占用的埠號；每次啟動伺服器都使用新埠號，避免 TIME_WAIT 或殘留行程的干擾。"""

    def __init__(self, base):
        self.next = base

    def __call__(self):
        for _ in range(500):
            p, self.next = self.next, self.next + 1
            if port_is_free(p):
                return p
        raise RuntimeError("找不到可用的埠號")


async def start_server(cmd, port, logdir, extra, wait=10.0):
    """啟動受測伺服器並等待它開始監聽（最多 wait 秒）。POSIX 上自成一個行程群組，方便連同 AI 子行程一起結束。"""
    args = split_cmd(cmd) + ["--port", str(port), "--log-dir", logdir] + list(extra)
    kw = {"start_new_session": True} if POSIX else {}
    proc = await asyncio.create_subprocess_exec(*args, stdin=asyncio.subprocess.DEVNULL,
                                                stdout=asyncio.subprocess.DEVNULL,
                                                stderr=asyncio.subprocess.DEVNULL, **kw)
    loop = asyncio.get_running_loop()
    deadline = loop.time() + wait
    while loop.time() < deadline and proc.returncode is None:
        try:
            _, w = await asyncio.open_connection("127.0.0.1", port)
            w.close()
            break
        except OSError:
            await asyncio.sleep(0.1)
    return proc


async def kill(proc):
    """強制結束伺服器及其子行程（重複呼叫無害）。"""
    if proc is None or getattr(proc, "_bc_reaped", False):
        return
    if POSIX:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError, OSError):
            pass
    if proc.returncode is None:
        try:
            proc.kill()
        except (ProcessLookupError, OSError):
            pass
    await proc.wait()
    proc._bc_reaped = True


async def stop(proc, timeout=10):
    """等伺服器自行結束（最多 timeout 秒），之後清除它留下的子行程。"""
    if proc is not None and proc.returncode is None:
        try:
            await asyncio.wait_for(proc.wait(), timeout)
        except asyncio.TimeoutError:
            pass
    await kill(proc)


class Server:
    """async with Server(...) as proc：離開區塊時一定結束伺服器。"""

    def __init__(self, cmd, port, logdir, extra):
        self.args = (cmd, port, logdir, extra)
        self.proc = None

    async def __aenter__(self):
        self.proc = await start_server(*self.args)
        return self.proc

    async def __aexit__(self, *exc):
        await kill(self.proc)
        return False


async def wait_with_progress(proc, logdir, total, idle):
    """等伺服器自行結束；總時間超過 total 秒，或日誌連續 idle 秒沒有任何增長時，拋出 TimeoutError。"""
    loop = asyncio.get_running_loop()
    start = last_change = loop.time()
    last_size = -1
    while proc.returncode is None:
        try:
            await asyncio.wait_for(proc.wait(), 1.0)
            break
        except asyncio.TimeoutError:
            pass
        size = sum(os.path.getsize(f) for f in log_files(logdir)) if os.path.isdir(logdir) else 0
        now = loop.time()
        if size != last_size:
            last_size, last_change = size, now
        if now - last_change > idle:
            raise asyncio.TimeoutError(f"日誌連續 {idle} 秒沒有任何增長，伺服器可能卡住")
        if now - start > total:
            raise asyncio.TimeoutError(f"超過 {total} 秒仍未結束")


def log_files(d):
    """日誌目錄中的檔案（規範要求該目錄只有伺服器日誌，每局一檔）。"""
    return sorted(f for f in glob.glob(os.path.join(d, "*")) if os.path.isfile(f))


def iter_log(path):
    """逐筆讀出日誌紀錄，略過無法解析或結構不符的行。"""
    with open(path, encoding="utf-8", errors="replace") as f:
        for line in f:
            try:
                r = json.loads(line)
            except ValueError:
                continue
            if isinstance(r, dict) and isinstance(r.get("msg"), dict):
                yield r


FAST = ["--guess-timeout", "1.5", "--feedback-timeout", "1.5", "--commit-timeout", "2",
        "--reveal-timeout", "1.5"]


async def scripted(raw, name, *, lie=None, mute=False, afk=False, quit_at=None, no_commit=False,
                   fake_secret=None, reveal_override=None, secret=None):
    """可設定各種不良行為的腳本玩家；回傳 (player_id, 真正的秘密)。"""
    w = await raw.hello(name)
    if not w:
        raise RuntimeError(f"{name} 未收到 WELCOME")
    me = w.get("player_id")
    secret = secret or random.choice(ALL_NUMBERS)
    salt = secrets.token_hex(16)
    while True:
        m = await raw.recv(30)
        if m is None:
            return me, secret
        t = m.get("type")
        if t == "GAME_START" and not no_commit:
            raw.send({"type": "COMMIT", "commit": make_commit(secret, salt)})
        elif t == "TURN":
            if quit_at and m.get("turn_id", 0) >= quit_at:
                raw.close()
                return me, secret
            if m.get("guesser") == me and not afk:
                raw.send({"type": "GUESS", "turn_id": m.get("turn_id"), "guess": random.choice(ALL_NUMBERS)})
        elif t == "GUESS_MADE" and me in m.get("responders", []) and not mute:
            if lie == "zero":
                a, b = 0, 0
            elif fake_secret:
                a, b = score(m.get("guess", ""), fake_secret)
            else:
                a, b = score(m.get("guess", ""), secret)
            raw.send({"type": "FEEDBACK", "turn_id": m.get("turn_id"), "a": a, "b": b})
        elif t == "REVEAL_REQUEST":
            raw.send({"type": "REVEAL", "secret": reveal_override or secret, "salt": salt})
        elif t == "GAME_OVER":
            return me, secret


def last(raw, mtype):
    xs = [m for m in raw.inbox if m.get("type") == mtype]
    return xs[-1] if xs else None


def row_of(over, pid):
    for r in (over or {}).get("ranking", []):
        if isinstance(r, dict) and r.get("player") == pid:
            return r
    return {}


# ---------------------------------------------------------------------------
# [1] 純 AI 對局
# ---------------------------------------------------------------------------
async def test_bot_games(cmd, ports, logdir, n):
    d = os.path.join(logdir, f"bots{n}")
    async with Server(cmd, ports(), d, ["--players", str(n), "--bots", str(n), "--games", "10"]) as proc:
        await wait_with_progress(proc, d, total=600, idle=60)
    overs, verdicts = [], []
    for fn in log_files(d):
        seen_over, first_pid = None, None
        for rec in iter_log(fn):
            msg = rec["msg"]
            if rec.get("dir") != "send":
                continue
            if msg.get("type") == "WELCOME" and first_pid is None:
                first_pid = msg.get("player_id")
            if msg.get("type") == "GAME_OVER" and seen_over is None:
                seen_over = msg
            # 每則 REVEALED 都廣播給所有人，只取送給某一位玩家的那一份計數
            if msg.get("type") == "REVEALED" and rec.get("peer") == (first_pid or "p1"):
                verdicts.append(msg.get("verdict"))
        overs.append(seen_over)
    ok = all(o and o.get("reason") == "LAST_PLAYER"
             and sum(1 for r in o.get("ranking", []) if r.get("rank") == 1) == 1
             and len(o.get("ranking", [])) == n for o in overs)
    check(len(overs) == 10 and ok, f"{n} 人：10 局皆正常結束且恰有一位第一名", f"{len(overs)} 個日誌檔")
    check(bool(verdicts) and all(v == "OK" for v in verdicts), f"{n} 人：所有揭示驗證皆為 OK",
          f"共 {len(verdicts)} 則 REVEALED")
    turns = [o.get("turns") for o in overs if o and isinstance(o.get("turns"), int)]
    if turns:
        print(f"    {n} 人對局回合數：最少 {min(turns)}、平均 {sum(turns) / len(turns):.1f}、最多 {max(turns)}")


# ---------------------------------------------------------------------------
# [2] 連線與欄位錯誤處理
# ---------------------------------------------------------------------------
async def test_lobby_errors(cmd, ports, logdir):
    port = ports()
    async with Server(cmd, port, os.path.join(logdir, "lobby_err"), ["--players", "3"] + FAST):
        r = Raw(port)
        await r.connect()
        r.send(b"this is not json\n")
        check(is_err(await r.recv(), "BAD_JSON", False), "非 JSON → BAD_JSON（非致命）")
        r.send({"type": "PING"})
        check(is_err(await r.recv(), "UNEXPECTED", True), "HELLO 之前送其他訊息 → UNEXPECTED（致命）")
        check(await r.closed_within(5), "致命錯誤後伺服器關閉連線")
        r.close()

        r = Raw(port)
        await r.connect()
        r.send({"type": "HELLO", "protocol": "BC/2.0", "name": "x", "team": "T", "kind": "human"})
        check(is_err(await r.recv(), "VERSION_UNSUPPORTED", True), "主版本不符 → VERSION_UNSUPPORTED")
        r.close()

        r = Raw(port)
        await r.connect()
        r.send({"type": "HELLO", "protocol": "BC/1.0", "name": "x", "team": "T"})
        check(is_err(await r.recv(), "BAD_FIELD", True), "HELLO 缺 kind → BAD_FIELD（致命）")
        r.close()

        r = Raw(port)
        await r.connect()
        r.send({"type": "HELLO", "protocol": "BC/1.0", "name": "", "team": "T", "kind": "human"})
        check(is_err(await r.recv(), "INVALID_VALUE", True), "HELLO 空白名稱 → INVALID_VALUE（致命）")
        r.close()

        r = Raw(port)
        await r.connect()
        r.send(b"{" + b"x" * 5000 + b"}\n")
        check(is_err(await r.recv(), "LINE_TOO_LONG", True), "單行超過 4096 位元組 → LINE_TOO_LONG")
        r.close()

        r = Raw(port)
        await r.connect()
        check(is_err(await r.recv(15), "TIMEOUT", True), "連線後 10 秒未送 HELLO → TIMEOUT")
        r.close()


async def test_game_errors(cmd, ports, logdir):
    # 3 人局：伺服器自帶 1 個 AI，加上本測試的「測試者」與一位誠實的腳本玩家
    port = ports()
    async with Server(cmd, port, os.path.join(logdir, "game_err"), ["--players", "3", "--bots", "1"] + FAST):
        p = Raw(port)
        w = await p.hello("測試者")
        check(bool(w) and w.get("protocol") == "BC/1.0" and str(w.get("player_id", "")).startswith("p"),
              "合法 HELLO → WELCOME")
        if not w:
            raise RuntimeError("測試者未收到 WELCOME，無法繼續")
        me = w["player_id"]
        r = Raw(port)
        await r.connect()
        r.send({"type": "HELLO", "protocol": "BC/1.0", "name": "測試者", "team": "T", "kind": "human"})
        check(is_err(await r.recv(), "NAME_TAKEN", True), "名稱重複 → NAME_TAKEN")
        r.close()
        helper = asyncio.create_task(scripted(Raw(port), "誠實者"))
        try:
            gs = await p.expect("GAME_START", 15)
            check(bool(gs) and set(gs.get("rules", {})) >= {"guess_timeout", "feedback_timeout", "commit_timeout",
                                                           "reveal_timeout", "max_turns", "max_skips"},
                  "人數到齊 → GAME_START 含完整 rules")
            r2 = Raw(port)
            await r2.connect()
            r2.send({"type": "HELLO", "protocol": "BC/1.0", "name": "late", "team": "T", "kind": "human"})
            check(is_err(await r2.recv(), "GAME_IN_PROGRESS"), "開局後加入 → GAME_IN_PROGRESS")
            r2.close()

            secret, salt = random.choice(ALL_NUMBERS), secrets.token_hex(16)
            p.send({"type": "GUESS", "turn_id": 1, "guess": "0123"})
            check(is_err(await p.expect("ERROR"), "UNEXPECTED"), "承諾階段喊數 → UNEXPECTED")
            p.send({"type": "COMMIT", "commit": "XYZ"})
            check(is_err(await p.expect("ERROR"), "INVALID_VALUE"), "承諾值格式錯誤 → INVALID_VALUE")
            commit = make_commit(secret, salt)
            p.send(b"".join((json.dumps(x) + "\n").encode() for x in (
                {"type": "COMMIT", "commit": commit}, {"type": "COMMIT", "commit": commit})))
            check(is_err(await p.expect("ERROR"), "DUPLICATE"), "重複 COMMIT → DUPLICATE")
            cm = await p.expect("COMMITS", 10)
            check(bool(cm) and cm.get("commits", {}).get(me) == commit, "COMMITS 廣播所有承諾值")

            p.send({"type": "PING", "nonce": "n-42"})
            p.send({"type": "CHAT", "text": "大家好"})
            p.send({"type": "WHATEVER"})
            m = await p.expect("ERROR")
            got = [x for x in p.inbox if x.get("type") in ("PONG", "CHAT")]
            check(any(x.get("type") == "PONG" and x.get("nonce") == "n-42" for x in got), "PING → PONG 並回傳 nonce")
            check(any(x.get("type") == "CHAT" and x.get("from") == me and x.get("text") == "大家好" for x in got),
                  "CHAT 由伺服器轉播")
            check(is_err(m, "UNKNOWN_TYPE"), "未知類型 → UNKNOWN_TYPE")

            tested_guess = tested_fb = tested_nyt = False
            while True:
                m = await p.recv(30)
                if m is None or m.get("type") == "GAME_OVER":
                    break
                t = m.get("type")
                if t == "TURN":
                    tid = m.get("turn_id")
                    if m.get("guesser") == me:
                        if not tested_guess:
                            p.send({"type": "GUESS", "turn_id": True, "guess": "0123"})
                            e1 = await p.expect("ERROR")
                            p.send({"type": "GUESS", "turn_id": tid + 5, "guess": "4567"})
                            e2 = await p.expect("ERROR")
                            p.send({"type": "GUESS", "turn_id": tid, "guess": "1123"})
                            e3 = await p.expect("ERROR")
                            check(is_err(e1, "BAD_FIELD"), "turn_id 為布林值 → BAD_FIELD")
                            check(is_err(e2, "STALE_TURN"), "turn_id 不符 → STALE_TURN")
                            check(is_err(e3, "INVALID_VALUE"), "數字重複的喊數 → INVALID_VALUE")
                            tested_guess = True
                        p.send({"type": "GUESS", "turn_id": tid, "guess": random.choice(ALL_NUMBERS)})
                    elif not tested_nyt:
                        p.send({"type": "GUESS", "turn_id": tid, "guess": "4567"})
                        check(is_err(await p.expect("ERROR"), "NOT_YOUR_TURN"), "非喊數者喊數 → NOT_YOUR_TURN")
                        tested_nyt = True
                elif t == "GUESS_MADE" and me in m.get("responders", []):
                    a, b = score(m.get("guess", ""), secret)
                    if not tested_fb:
                        p.send({"type": "FEEDBACK", "turn_id": m.get("turn_id"), "a": 3, "b": 1})
                        check(is_err(await p.expect("ERROR"), "INVALID_VALUE"), "回報 3A1B → INVALID_VALUE")
                        p.send(b"".join((json.dumps(x) + "\n").encode() for x in (
                            {"type": "FEEDBACK", "turn_id": m.get("turn_id"), "a": a, "b": b},
                            {"type": "FEEDBACK", "turn_id": m.get("turn_id"), "a": a, "b": b})))
                        check(is_err(await p.expect("ERROR"), "DUPLICATE"), "重複回報 → DUPLICATE")
                        tested_fb = True
                    else:
                        p.send({"type": "FEEDBACK", "turn_id": m.get("turn_id"), "a": a, "b": b})
                elif t == "REVEAL_REQUEST":
                    p.send({"type": "REVEAL", "secret": secret, "salt": salt})
            over = last(p, "GAME_OVER")
            check(bool(over) and over.get("reason") in ("LAST_PLAYER", "MAX_TURNS"), "錯誤測試後遊戲仍正常結束")
            rv = [x for x in p.inbox if x.get("type") == "REVEALED" and x.get("player") == me]
            check(bool(rv) and rv[0].get("verdict") == "OK", "誠實玩家揭示驗證 OK")
            await asyncio.wait_for(helper, 40)
        finally:
            helper.cancel()


# ---------------------------------------------------------------------------
# [3] 說謊、斷線、逾時與棄權
# ---------------------------------------------------------------------------
async def test_liar(cmd, ports, logdir):
    # 明顯說謊（永遠回報 0A0B）→ 公開一致性檢查取消資格
    port = ports()
    async with Server(cmd, port, os.path.join(logdir, "liar"), ["--players", "2", "--bots", "1"] + FAST):
        r = Raw(port)
        me, _ = await scripted(r, "liar", lie="zero")
        over = last(r, "GAME_OVER")
        dq_turn = [m for m in r.inbox if m.get("type") == "TURN_RESULT" and me in m.get("disqualified", [])]
        check(bool(dq_turn), "永遠回報 0A0B → 在 TURN_RESULT 的 disqualified 中被取消資格")
        row = row_of(over, me)
        check(row.get("status") == "DQ" and "rank" in row and row["rank"] is None, "被取消資格者在 GAME_OVER 無名次")


async def test_liar2(cmd, ports, logdir):
    # 一致地假裝另一個數字，被猜中假數字時承認 4A，揭示真數字 → INCONSISTENT
    port = ports()
    async with Server(cmd, port, os.path.join(logdir, "liar2"),
                      ["--players", "2", "--bots", "1", "--max-turns", "60"] + FAST):
        r = Raw(port)
        real, fake = random.sample(ALL_NUMBERS, 2)
        me, _ = await scripted(r, "liar2", fake_secret=fake, secret=real)
        rv = [m for m in r.inbox if m.get("type") == "REVEALED" and m.get("player") == me]
        over = last(r, "GAME_OVER")
        check(bool(rv) and rv[0].get("verdict") == "INCONSISTENT", "一致地假裝另一個秘密 → 揭示判定 INCONSISTENT",
              f"假秘密 {fake}、真秘密 {real}、判定 {rv[0].get('verdict') if rv else None}、"
              f"bad_turns={rv[0].get('bad_turns') if rv else None}")
        check(row_of(over, me).get("status") == "DQ", "一致說謊者終局驗證後取消名次")


async def test_badcommit(cmd, ports, logdir):
    # 揭示時謊報秘密 → BAD_COMMIT
    port = ports()
    async with Server(cmd, port, os.path.join(logdir, "badcommit"), ["--players", "2", "--bots", "1"] + FAST):
        r = Raw(port)
        real = random.choice([x for x in ALL_NUMBERS if x != "0123"])
        me, _ = await scripted(r, "badrev", reveal_override="0123", secret=real)
        rv = [m for m in r.inbox if m.get("type") == "REVEALED" and m.get("player") == me]
        check(bool(rv) and rv[0].get("verdict") == "BAD_COMMIT", "揭示的秘密與承諾值不符 → BAD_COMMIT")


async def test_quit(cmd, ports, logdir):
    # 中途斷線 → 棄權，名次排在所有被猜中者之後（由日誌檢查）
    port = ports()
    d = os.path.join(logdir, "quit")
    async with Server(cmd, port, d, ["--players", "4", "--bots", "3"] + FAST) as proc:
        r = Raw(port)
        me, _ = await scripted(r, "quitter", quit_at=3)
        await stop(proc, 60)
    over, tr = None, None
    files = log_files(d)
    for rec in (iter_log(files[0]) if files else []):
        mm = rec["msg"]
        if rec.get("dir") == "send" and mm.get("type") == "TURN_RESULT" and me in mm.get("forfeited", []) \
                and tr is None:
            tr = mm
        if rec.get("dir") == "send" and mm.get("type") == "GAME_OVER":
            over = mm
    check(tr is not None, "斷線玩家出現在 TURN_RESULT 的 forfeited")
    mine = row_of(over, me)
    others = [x for x in (over or {}).get("ranking", []) if x.get("status") in ("GUESSED", "SURVIVOR")]
    check(bool(over) and mine.get("status") == "FORFEIT" and isinstance(mine.get("rank"), int)
          and all(isinstance(x.get("rank"), int) and mine["rank"] > x["rank"] for x in others),
          "棄權者名次低於所有被猜中者與存活者")


async def test_mute(cmd, ports, logdir):
    port = ports()
    async with Server(cmd, port, os.path.join(logdir, "mute"), ["--players", "3", "--bots", "2"] + FAST):
        r = Raw(port)
        me, _ = await scripted(r, "mute", mute=True)
        tr = [m for m in r.inbox if m.get("type") == "TURN_RESULT" and me in m.get("forfeited", [])]
        check(bool(tr) and tr[0].get("skipped") is False, "回報逾時 → 該回合 forfeited")


async def test_afk(cmd, ports, logdir):
    # 輪到時不喊數（afk）→ 跳過，連續 max_skips 次後棄權
    port = ports()
    async with Server(cmd, port, os.path.join(logdir, "afk"),
                      ["--players", "2", "--bots", "1", "--max-skips", "2"] + FAST):
        r = Raw(port)
        me, _ = await scripted(r, "afk", afk=True)
        skips = [m for m in r.inbox if m.get("type") == "TURN_RESULT" and m.get("guesser") == me and m.get("skipped")]
        forf = [m for m in r.inbox if m.get("type") == "TURN_RESULT" and me in m.get("forfeited", [])]
        over = last(r, "GAME_OVER")
        label = "連續 2 次逾時未喊數 → 第 2 次跳過時棄權"
        if forf:
            check(len(skips) == 2 and forf[0] is skips[-1], label, f"跳過 {len(skips)} 次")
        else:
            check(row_of(over, me).get("status") == "GUESSED" and len(skips) < 2, label,
                  "afk 玩家在第 2 次跳過前就被猜中，本次不具鑑別力")


async def test_nocommit(cmd, ports, logdir):
    port = ports()
    async with Server(cmd, port, os.path.join(logdir, "nocommit"), ["--players", "3", "--bots", "2"] + FAST):
        r = Raw(port)
        await scripted(r, "nocommit", no_commit=True)
        e = [m for m in r.inbox if m.get("type") == "ERROR"]
        check(bool(e) and is_err(e[-1], "TIMEOUT", True), "承諾逾時 → ERROR TIMEOUT 並移出本局")


async def test_abort(cmd, ports, logdir):
    port = ports()
    d = os.path.join(logdir, "abort")
    async with Server(cmd, port, d, ["--players", "2", "--bots", "1"] + FAST) as proc:
        r = Raw(port)
        await scripted(r, "nocommit2", no_commit=True)
        await stop(proc, 15)
    files = log_files(d)
    reasons = [rec["msg"].get("reason") for rec in (iter_log(files[0]) if files else [])
               if rec.get("dir") == "send" and rec["msg"].get("type") == "GAME_OVER"]
    check(bool(reasons) and reasons[0] == "ABORTED", "承諾後不足 2 人 → GAME_OVER ABORTED")


# ---------------------------------------------------------------------------
async def main():
    here = os.path.dirname(os.path.abspath(__file__))
    ap = argparse.ArgumentParser(description="BC/1.0 伺服器協定自我測試工具（48 項）")
    ap.add_argument("--server", default=f"{shlex.quote(sys.executable)} {shlex.quote(os.path.join(here, 'bc.py'))} server",
                    help="啟動受測伺服器的命令（不含 --port 與 --log-dir）")
    ap.add_argument("--port", type=int, default=5600, help="起始埠號（預設 5600）")
    ap.add_argument("--skip-bots", action="store_true", help="略過第 [1] 節的純 AI 對局")
    ap.add_argument("--json", help="把逐項結果另存為 JSON 檔")
    a = ap.parse_args()
    logdir = tempfile.mkdtemp(prefix="bc-selftest-")
    ports = Ports(a.port)
    cmd = a.server

    if a.skip_bots:
        for n in range(2, 7):
            SKIPPED.extend(LABELS[f"bots{n}"])
        print("\n[1] 純 AI 對局：已略過（--skip-bots）")
    else:
        print("\n[1] 純 AI 對局：2–6 人各 10 局", flush=True)
        for n in range(2, 7):
            await run_section(f"bots{n}", None, test_bot_games, cmd, ports, logdir, n)
    await run_section("lobby_errors", "[2] 連線與欄位錯誤處理", test_lobby_errors, cmd, ports, logdir)
    await run_section("game_errors", None, test_game_errors, cmd, ports, logdir)
    print("\n[3] 說謊、斷線、逾時與棄權", flush=True)
    for key, fn in (("liar", test_liar), ("liar2", test_liar2), ("badcommit", test_badcommit),
                    ("quit", test_quit), ("mute", test_mute), ("afk", test_afk),
                    ("nocommit", test_nocommit), ("abort", test_abort)):
        await run_section(key, None, fn, cmd, ports, logdir)

    passed = [l for l in ALL_LABELS if RESULTS.get(l, (False,))[0]]
    failed = [l for l in ALL_LABELS if l in RESULTS and not RESULTS[l][0]]
    print(f"\n通過 {len(passed)} 項，失敗 {len(failed)} 項" + (f"，略過 {len(SKIPPED)} 項" if SKIPPED else "")
          + f"（共 {len(ALL_LABELS)} 項）。日誌：{logdir}")
    for f in failed:
        print("  失敗：", f, f"（{RESULTS[f][1]}）" if RESULTS[f][1] else "")
    if a.json:
        checks = [{"group": "A1", "label": l, "ok": RESULTS.get(l, (False,))[0],
                   "note": RESULTS[l][1] if l in RESULTS else "略過"} for l in ALL_LABELS]
        with open(a.json, "w", encoding="utf-8") as f:
            json.dump({"tool": "bc_selftest", "total": len(ALL_LABELS), "passed": len(passed),
                       "skipped": SKIPPED, "checks": checks, "logdir": logdir}, f, ensure_ascii=False, indent=2)
        print(f"結果已存成 {a.json}")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    asyncio.run(main())
