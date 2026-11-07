#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
bc.py — 幾A幾B（Bulls and Cows）多人網路對戰協定 BC/1.0 參考原型

同一支程式依子命令扮演三種身分：
    python bc.py server [--port 5040] [--players 3] [--bots 1] [...]
    python bc.py client --host HOST [--port 5040] --name 名字 [--team G00]
    python bc.py ai     --host HOST [--port 5040] --name 名字 [--team G00]

只使用 Python 3.10 以上的標準函式庫。
"""
from __future__ import annotations

import argparse
import asyncio
import hashlib
import itertools
import json
import os
import random
import re
import secrets
import sys
import threading
import time
import unicodedata
import uuid

# ---------------------------------------------------------------------------
# 協定常數與共用函式
# ---------------------------------------------------------------------------
PROTOCOL = "BC/1.0"
SOFTWARE = "BC-ref/0.9"
DEFAULT_PORT = 5040
MAX_LINE = 4096          # 單一訊息（含結尾 LF）最大位元組數
HELLO_TIMEOUT = 10.0     # 連線後必須在此秒數內送出 HELLO
MAX_ERRORS = 20          # 單一連線累積非致命錯誤上限
MAX_OUTQUEUE = 1000      # 單一連線待送訊息上限（防止慢速客戶端拖垮伺服器）

DIGITS_RE = re.compile(r"[0-9]{4}")
HEX64_RE = re.compile(r"[0-9a-f]{64}")
HEX32_RE = re.compile(r"[0-9a-f]{32}")
VERSION_RE = re.compile(r"BC/1\.[0-9]+")

ALL_NUMBERS = ["".join(p) for p in itertools.permutations("0123456789", 4)]  # 5040 個
VALID_FEEDBACK = frozenset(
    (a, b) for a in range(5) for b in range(5) if a + b <= 4 and (a, b) != (3, 1)
)  # 14 種


def valid_number(x) -> bool:
    """四個 ASCII 數字且兩兩相異（允許首位為 0）。"""
    return isinstance(x, str) and DIGITS_RE.fullmatch(x) is not None and len(set(x)) == 4


def is_int(x) -> bool:
    """JSON 整數；排除 Python 中屬於 int 子類別的 bool。"""
    return isinstance(x, int) and not isinstance(x, bool)


def valid_text(x, lo: int, hi: int) -> bool:
    """長度介於 lo..hi 個字元、且不含控制字元的字串。"""
    return (isinstance(x, str) and lo <= len(x) <= hi
            and not any(unicodedata.category(c).startswith("C") for c in x))


def score(guess: str, secret: str) -> tuple[int, int]:
    a = sum(g == s for g, s in zip(guess, secret))
    b = len(set(guess) & set(secret)) - a
    return a, b


def make_commit(secret: str, salt: str) -> str:
    return hashlib.sha256(f"{secret}:{salt}".encode("ascii")).hexdigest()


def encode(msg: dict) -> bytes:
    return (json.dumps(msg, ensure_ascii=False, separators=(",", ":"), allow_nan=False) + "\n").encode("utf-8")


def _reject_constant(name):
    raise ValueError(f"{name} 不是合法的 JSON 數值")


def decode_line(raw: bytes):
    """回傳 (msg, err)。空白行回傳 (None, None)；格式錯誤回傳 (None, 'BAD_JSON')。"""
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError:
        return None, "BAD_JSON"
    if text.endswith("\n"):
        text = text[:-1]
    if text.endswith("\r"):
        text = text[:-1]
    if text.strip() == "":
        return None, None
    try:
        msg = json.loads(text, parse_constant=_reject_constant)
    except ValueError:
        return None, "BAD_JSON"
    if not isinstance(msg, dict) or not isinstance(msg.get("type"), str):
        return None, "BAD_JSON"
    return msg, None


def verify_reveal(commit, records, secret, salt):
    """依承諾值與公開回報紀錄判定揭示結果，回傳 (verdict, bad_turns)。"""
    if secret is None or salt is None:
        return "NO_REVEAL", []
    if make_commit(secret, salt) != commit:
        return "BAD_COMMIT", []
    bad = [t for (t, g, a, b) in records if score(g, secret) != (a, b)]
    return ("INCONSISTENT", bad) if bad else ("OK", [])


def compute_ranking(entries):
    """entries: [(pid, status, out_turn)]；status ∈ SURVIVOR/GUESSED/FORFEIT/DQ。
    回傳 [(pid, status, out_turn, rank)]，DQ 的 rank 為 None；採標準競賽排名（1,2,2,4）。"""
    cat = {"SURVIVOR": 0, "GUESSED": 1, "FORFEIT": 2}

    def key(e):
        pid, st, t = e
        return (cat[st], 0 if st == "SURVIVOR" else -t)

    ranked = [e for e in entries if e[1] != "DQ"]
    keys = [key(e) for e in ranked]
    out = []
    for e, k in sorted(zip(ranked, keys), key=lambda x: x[1]):
        rank = 1 + sum(1 for k2 in keys if k2 < k)
        out.append((e[0], e[1], e[2], rank))
    out += [(pid, st, t, None) for (pid, st, t) in entries if st == "DQ"]
    return out


# ---------------------------------------------------------------------------
# 伺服器
# ---------------------------------------------------------------------------
class Player:
    def __init__(self, pid, name, team, kind, conn):
        self.pid, self.name, self.team, self.kind, self.conn = pid, name, team, kind, conn
        self.status = "LOBBY"     # LOBBY → ALIVE → GUESSED / FORFEIT / DQ；或 REMOVED
        self.commit = None
        self.records = []         # [(turn_id, guess, a, b)]
        self.cands = list(ALL_NUMBERS)
        self.skips = 0
        self.out_turn = None
        self.reveal = None        # (secret, salt)

    @property
    def connected(self):
        return not self.conn.closed

    def public(self):
        return {"id": self.pid, "name": self.name, "team": self.team, "kind": self.kind}


class Conn:
    def __init__(self, srv, reader, writer):
        self.srv, self.reader, self.writer = srv, reader, writer
        peer = writer.get_extra_info("peername")
        self.addr = f"{peer[0]}:{peer[1]}" if peer else "?"
        self.player: Player | None = None
        self.errors = 0
        self.closed = False
        self.outq: asyncio.Queue = asyncio.Queue()
        self.writer_task = asyncio.create_task(self._writer())

    def label(self):
        return self.player.pid if self.player else self.addr

    def send(self, msg):
        if self.closed:
            return
        if self.outq.qsize() > MAX_OUTQUEUE:
            self.close()
            return
        self.srv.log("send", self.label(), msg)
        self.outq.put_nowait(encode(msg))

    def error(self, code, message, fatal=False):
        self.errors += 1
        self.send({"type": "ERROR", "code": code, "message": message, "fatal": fatal})
        if fatal:
            self.close()
        elif self.errors > MAX_ERRORS:
            self.send({"type": "ERROR", "code": "TOO_MANY_ERRORS",
                       "message": "累積錯誤過多，連線即將關閉", "fatal": True})
            self.close()

    def close(self):
        """送完佇列中的訊息後關閉連線。"""
        if not self.closed:
            self.closed = True
            self.outq.put_nowait(None)
            self.srv.changed.set()

    async def _writer(self):
        try:
            while True:
                data = await self.outq.get()
                if data is None:
                    break
                self.writer.write(data)
                await self.writer.drain()
        except (ConnectionError, OSError):
            pass
        finally:
            self.closed = True
            try:
                self.writer.close()
            except Exception:
                pass
            self.srv.changed.set()


class Server:
    def __init__(self, args):
        self.a = args
        self.players: dict[str, Player] = {}
        self.conns: set[Conn] = set()
        self.phase = "LOBBY"
        self.changed = asyncio.Event()
        self.next_id = 1
        self.game_id = None
        self.logf = None
        self.manual_start = False
        # 回合狀態
        self.turn_id = 0
        self.guesser = None
        self.guess_open = False
        self.cur_guess = None
        self.fb_open = False
        self.responders = []
        self.feedback = {}
        self.reveal_wait = set()
        self.bot_procs = []

    # ----- 紀錄 -----
    def log(self, direction, peer, msg):
        if self.logf:
            rec = {"ts": round(time.time(), 3), "dir": direction, "peer": peer, "msg": msg}
            self.logf.write(json.dumps(rec, ensure_ascii=False) + "\n")
            self.logf.flush()

    def say(self, text):
        print(f"[server] {text}", flush=True)

    # ----- 廣播 -----
    def broadcast(self, msg):
        for p in list(self.players.values()):
            if p.status != "REMOVED" and p.connected:
                p.conn.send(msg)

    def broadcast_lobby(self):
        self.broadcast({"type": "LOBBY",
                        "players": [p.public() for p in self.players.values()],
                        "min_players": 2, "max_players": self.a.players})

    # ----- 連線處理 -----
    async def handle_conn(self, reader, writer):
        conn = Conn(self, reader, writer)
        self.conns.add(conn)
        loop = asyncio.get_running_loop()
        deadline = loop.time() + HELLO_TIMEOUT
        try:
            while not conn.closed:
                try:
                    if conn.player is None:
                        raw = await asyncio.wait_for(reader.readline(),
                                                     max(0.01, deadline - loop.time()))
                    else:
                        raw = await reader.readline()
                except asyncio.TimeoutError:
                    conn.error("TIMEOUT", "未在時限內送出 HELLO", fatal=True)
                    break
                except ValueError:
                    conn.error("LINE_TOO_LONG", f"單行訊息超過 {MAX_LINE} 位元組", fatal=True)
                    break
                except (ConnectionError, OSError):
                    break
                if not raw:
                    break
                if len(raw) > MAX_LINE:
                    conn.error("LINE_TOO_LONG", f"單行訊息超過 {MAX_LINE} 位元組", fatal=True)
                    break
                msg, err = decode_line(raw)
                self.log("recv", conn.label(), msg if msg is not None
                         else {"raw": raw.decode("utf-8", "replace")})
                if err:
                    conn.error(err, "無法解析為含 type 欄位的 JSON 物件")
                    continue
                if msg is not None:
                    self.dispatch(conn, msg)
        finally:
            conn.close()
            self.conns.discard(conn)
            self.on_disconnect(conn)

    def on_disconnect(self, conn):
        p = conn.player
        if p is None:
            return
        if self.phase == "LOBBY" and p.status == "LOBBY" and self.players.get(p.pid) is p:
            del self.players[p.pid]
            self.say(f"{p.pid} {p.name} 離開大廳")
            self.broadcast_lobby()
        self.changed.set()

    def dispatch(self, conn, msg):
        t = msg["type"]
        if conn.player is None:
            if t != "HELLO":
                conn.error("UNEXPECTED", "第一則訊息必須是 HELLO", fatal=True)
                return
            self.on_hello(conn, msg)
            return
        handler = {
            "HELLO": lambda c, m: c.error("UNEXPECTED", "已完成 HELLO"),
            "COMMIT": self.on_commit, "GUESS": self.on_guess, "FEEDBACK": self.on_feedback,
            "REVEAL": self.on_reveal, "CHAT": self.on_chat, "PING": self.on_ping,
            "PONG": lambda c, m: None, "BYE": lambda c, m: c.close(),
        }.get(t)
        if handler is None:
            conn.error("UNKNOWN_TYPE", f"不支援的訊息類型 {t}")
        else:
            handler(conn, msg)

    def on_hello(self, conn, m):
        if not all(isinstance(m.get(k), str) for k in ("protocol", "name", "team", "kind")):
            conn.error("BAD_FIELD", "HELLO 需要字串欄位 protocol、name、team、kind", fatal=True)
            return
        if VERSION_RE.fullmatch(m["protocol"]) is None:
            conn.error("VERSION_UNSUPPORTED", f"本伺服器使用 {PROTOCOL}", fatal=True)
            return
        if not (valid_text(m["name"], 1, 20) and valid_text(m["team"], 1, 20)
                and m["kind"] in ("human", "ai")):
            conn.error("INVALID_VALUE", "name/team 須為 1–20 字且不含控制字元；kind 須為 human 或 ai",
                       fatal=True)
            return
        if self.phase != "LOBBY":
            conn.error("GAME_IN_PROGRESS", "遊戲進行中，無法加入", fatal=True)
            return
        if len(self.players) >= self.a.players:
            conn.error("ROOM_FULL", "人數已滿", fatal=True)
            return
        if any(p.name == m["name"] for p in self.players.values()):
            conn.error("NAME_TAKEN", "名稱已被使用", fatal=True)
            return
        pid = f"p{self.next_id}"
        self.next_id += 1
        p = Player(pid, m["name"], m["team"], m["kind"], conn)
        self.players[pid] = p
        conn.player = p
        conn.send({"type": "WELCOME", "protocol": PROTOCOL, "player_id": pid, "server": SOFTWARE})
        self.say(f"{pid} {p.name}（{p.team}, {p.kind}）加入，目前 {len(self.players)}/{self.a.players}")
        self.broadcast_lobby()
        self.changed.set()

    def on_commit(self, conn, m):
        p = conn.player
        c = m.get("commit")
        if not isinstance(c, str):
            conn.error("BAD_FIELD", "COMMIT 需要字串欄位 commit")
        elif self.phase != "COMMIT" or p.status != "ALIVE":
            conn.error("UNEXPECTED", "目前不接受 COMMIT")
        elif p.commit is not None:
            conn.error("DUPLICATE", "已送出過 COMMIT")
        elif HEX64_RE.fullmatch(c) is None:
            conn.error("INVALID_VALUE", "commit 須為 64 個小寫十六進位字元")
        else:
            p.commit = c
            self.changed.set()

    def on_guess(self, conn, m):
        p = conn.player
        t, g = m.get("turn_id"), m.get("guess")
        if not is_int(t) or not isinstance(g, str):
            conn.error("BAD_FIELD", "GUESS 需要整數 turn_id 與字串 guess")
        elif self.phase != "PLAY":
            conn.error("UNEXPECTED", "目前不在對局階段")
        elif t != self.turn_id:
            conn.error("STALE_TURN", f"目前回合為 {self.turn_id}")
        elif p.pid != self.guesser:
            conn.error("NOT_YOUR_TURN", f"本回合喊數者為 {self.guesser}")
        elif not self.guess_open:
            conn.error("UNEXPECTED", "本回合已不接受喊數")
        elif not valid_number(g):
            conn.error("INVALID_VALUE", "guess 須為四個互異的數字")
        else:
            self.cur_guess = g
            self.guess_open = False
            self.changed.set()

    def on_feedback(self, conn, m):
        p = conn.player
        t, a, b = m.get("turn_id"), m.get("a"), m.get("b")
        if not (is_int(t) and is_int(a) and is_int(b)):
            conn.error("BAD_FIELD", "FEEDBACK 需要整數 turn_id、a、b")
        elif self.phase != "PLAY":
            conn.error("UNEXPECTED", "目前不在對局階段")
        elif t != self.turn_id:
            conn.error("STALE_TURN", f"目前回合為 {self.turn_id}")
        elif not self.fb_open or p.pid not in self.responders:
            conn.error("UNEXPECTED", "你不需要回報本回合")
        elif p.pid in self.feedback:
            conn.error("DUPLICATE", "本回合已回報")
        elif (a, b) not in VALID_FEEDBACK:
            conn.error("INVALID_VALUE", "a、b 須滿足 a+b≤4 且不得為 3A1B")
        else:
            self.feedback[p.pid] = (a, b)
            self.changed.set()

    def on_reveal(self, conn, m):
        p = conn.player
        s, salt = m.get("secret"), m.get("salt")
        if not isinstance(s, str) or not isinstance(salt, str):
            conn.error("BAD_FIELD", "REVEAL 需要字串欄位 secret 與 salt")
        elif p.pid not in self.reveal_wait:
            conn.error("DUPLICATE" if p.reveal else "UNEXPECTED", "目前不需要揭示")
        elif not valid_number(s) or HEX32_RE.fullmatch(salt) is None:
            conn.error("INVALID_VALUE", "secret 須為四個互異數字，salt 須為 32 個小寫十六進位字元")
        else:
            p.reveal = (s, salt)
            self.reveal_wait.discard(p.pid)
            self.changed.set()

    def on_chat(self, conn, m):
        text = m.get("text")
        if not isinstance(text, str):
            conn.error("BAD_FIELD", "CHAT 需要字串欄位 text")
        elif not valid_text(text, 1, 200):
            conn.error("INVALID_VALUE", "text 須為 1–200 字且不含控制字元")
        else:
            self.broadcast({"type": "CHAT", "from": conn.player.pid, "text": text})

    def on_ping(self, conn, m):
        reply = {"type": "PONG"}
        if "nonce" in m:
            reply["nonce"] = m["nonce"]
        conn.send(reply)

    # ----- 等待工具 -----
    async def wait_until(self, cond, timeout):
        loop = asyncio.get_running_loop()
        deadline = None if timeout is None else loop.time() + timeout
        while True:
            if cond():
                return True
            remaining = None if deadline is None else deadline - loop.time()
            if remaining is not None and remaining <= 0:
                return False
            self.changed.clear()
            try:
                await asyncio.wait_for(self.changed.wait(), remaining)
            except asyncio.TimeoutError:
                return cond()

    # ----- 一局遊戲 -----
    async def run_game(self):
        a = self.a
        self.phase = "LOBBY"
        self.players = {}
        self.next_id = 1                      # player_id 每局自 p1 起編
        self.game_id = uuid.uuid4().hex[:12]
        os.makedirs(a.log_dir, exist_ok=True)
        stamp = time.strftime("%Y%m%d-%H%M%S")
        self.logf = open(os.path.join(a.log_dir, f"{stamp}-{self.game_id}.jsonl"), "w", encoding="utf-8")
        self.manual_start = False
        self.say(f"大廳開放（game_id={self.game_id}），等待 {a.players} 位玩家")
        await self.spawn_bots()

        await self.wait_until(lambda: len(self.players) >= a.players
                              or (self.manual_start and len(self.players) >= 2), None)

        # --- 承諾階段 ---
        self.phase = "COMMIT"
        order = list(self.players)
        random.shuffle(order)
        for p in self.players.values():
            p.status = "ALIVE"
        num = lambda x: int(x) if float(x).is_integer() else x  # noqa: E731  整數秒數以整數表示
        rules = {"guess_timeout": num(a.guess_timeout), "feedback_timeout": num(a.feedback_timeout),
                 "commit_timeout": num(a.commit_timeout), "reveal_timeout": num(a.reveal_timeout),
                 "max_turns": a.max_turns, "max_skips": a.max_skips}
        self.broadcast({"type": "GAME_START", "game_id": self.game_id,
                        "players": [self.players[pid].public() for pid in order],
                        "order": order, "rules": rules})
        self.say(f"遊戲開始，順序 {order}")
        P = self.players
        await self.wait_until(lambda: all(p.commit or not p.connected for p in P.values()),
                              a.commit_timeout)
        for p in P.values():
            if p.commit is None or not p.connected:
                p.status = "REMOVED"
                if p.connected:
                    p.conn.error("TIMEOUT", "未在時限內送出 COMMIT，已移出本局", fatal=True)
        order = [pid for pid in order if P[pid].status == "ALIVE"]
        if len(order) < 2:
            self.finish("ABORTED", 0, [])
            return
        self.broadcast({"type": "COMMITS", "order": order,
                        "commits": {pid: P[pid].commit for pid in order}})

        # --- 對局階段 ---
        self.phase = "PLAY"
        self.turn_id = 0
        last = -1
        reason = None
        while True:
            alive = [pid for pid in order if P[pid].status == "ALIVE"]
            if len(alive) <= 1:
                reason = "LAST_PLAYER"
                break
            if self.turn_id >= a.max_turns:
                reason = "MAX_TURNS"
                break
            self.turn_id += 1
            tid = self.turn_id
            n = len(order)
            idx = next(i % n for i in range(last + 1, last + 1 + n) if P[order[i % n]].status == "ALIVE")
            last = idx
            gid = order[idx]
            G = P[gid]
            self.guesser, self.cur_guess, self.guess_open = gid, None, True
            self.broadcast({"type": "TURN", "turn_id": tid, "guesser": gid, "alive": alive})
            await self.wait_until(lambda: self.cur_guess is not None or not G.connected, a.guess_timeout)
            self.guess_open = False
            guess = self.cur_guess
            results, elim, forf, dq = [], [], [], []
            if guess is None:
                if G.connected:
                    G.skips += 1
                    if G.skips >= a.max_skips:
                        forf.append(gid)
            else:
                G.skips = 0
                self.responders = [pid for pid in alive if pid != gid]
                self.feedback = {}
                self.fb_open = True
                self.broadcast({"type": "GUESS_MADE", "turn_id": tid, "guesser": gid,
                                "guess": guess, "responders": self.responders})
                await self.wait_until(
                    lambda: all(q in self.feedback or not P[q].connected for q in self.responders),
                    a.feedback_timeout)
                self.fb_open = False
                for q in self.responders:
                    if q not in self.feedback:
                        forf.append(q)
                        continue
                    fa, fb = self.feedback[q]
                    results.append({"player": q, "a": fa, "b": fb})
                    Q = P[q]
                    Q.records.append((tid, guess, fa, fb))
                    Q.cands = [s for s in Q.cands if score(guess, s) == (fa, fb)]
                    if not Q.cands:
                        dq.append(q)
                    elif (fa, fb) == (4, 0):
                        elim.append(q)
            for pid in alive:
                if pid not in forf and pid not in elim and pid not in dq and not P[pid].connected:
                    forf.append(pid)
            for pid, st in [(x, "GUESSED") for x in elim] + [(x, "FORFEIT") for x in forf] \
                    + [(x, "DQ") for x in dq]:
                P[pid].status, P[pid].out_turn = st, tid
            key = {pid: i for i, pid in enumerate(order)}
            self.broadcast({"type": "TURN_RESULT", "turn_id": tid, "guesser": gid, "guess": guess,
                            "skipped": guess is None, "results": results,
                            "eliminated": sorted(elim, key=key.get),
                            "forfeited": sorted(forf, key=key.get),
                            "disqualified": sorted(dq, key=key.get)})
            if elim:
                await self.collect_reveals(sorted(elim, key=key.get), "ELIMINATED")

        # --- 終局揭示 ---
        self.phase = "END"
        survivors = [pid for pid in order if P[pid].status == "ALIVE"]
        if survivors:
            await self.collect_reveals(survivors, "GAME_END")
        entries = []
        for pid in order:
            st = P[pid].status
            entries.append((pid, "SURVIVOR" if st == "ALIVE" else st, P[pid].out_turn))
        self.finish(reason, self.turn_id, compute_ranking(entries))

    async def collect_reveals(self, pids, reason):
        P = self.players
        self.reveal_wait = set(pids)
        for pid in pids:
            if P[pid].connected:
                P[pid].conn.send({"type": "REVEAL_REQUEST", "reason": reason})
        await self.wait_until(lambda: all(P[q].reveal or not P[q].connected for q in pids),
                              self.a.reveal_timeout)
        self.reveal_wait = set()
        for pid in pids:
            Q = P[pid]
            secret, salt = Q.reveal if Q.reveal else (None, None)
            verdict, bad = verify_reveal(Q.commit, Q.records, secret, salt)
            self.broadcast({"type": "REVEALED", "player": pid, "secret": secret, "salt": salt,
                            "verdict": verdict, "bad_turns": bad})
            if verdict != "OK":
                Q.status = "DQ"
                if Q.out_turn is None:
                    Q.out_turn = self.turn_id

    def finish(self, reason, turns, ranking):
        self.phase = "OVER"
        rows = [{"player": pid, "status": st, "out_turn": t, "rank": r} for pid, st, t, r in ranking]
        self.broadcast({"type": "GAME_OVER", "game_id": self.game_id, "reason": reason,
                        "turns": turns, "ranking": rows})
        self.say(f"遊戲結束（{reason}，共 {turns} 回合）")
        for row in rows:
            p = self.players[row["player"]]
            self.say(f"  名次 {row['rank']}  {p.pid} {p.name:<10} {row['status']}  out_turn={row['out_turn']}")
        for p in self.players.values():
            p.conn.close()

    async def spawn_bots(self):
        script = os.path.abspath(__file__)
        host = "127.0.0.1" if self.a.host in ("0.0.0.0", "", "::") else self.a.host
        for i in range(1, self.a.bots + 1):
            if self.a.bot_cmd:
                cmd = self.a.bot_cmd.format(host=host, port=self.a.port, name=f"BOT-{i}").split()
            else:
                cmd = [sys.executable, script, "ai", "--host", host, "--port", str(self.a.port),
                       "--name", f"BOT-{i}", "--team", "BOT", "--quiet"]
            proc = await asyncio.create_subprocess_exec(*cmd, stdin=asyncio.subprocess.DEVNULL)
            self.bot_procs.append(proc)

    async def reap_bots(self):
        for proc in self.bot_procs:
            try:
                await asyncio.wait_for(proc.wait(), 5)
            except asyncio.TimeoutError:
                proc.kill()
        self.bot_procs = []

    def start_console(self):
        if not sys.stdin or not sys.stdin.isatty():
            return
        loop = asyncio.get_running_loop()

        def reader():
            for line in sys.stdin:
                cmd = line.strip().lower()
                if cmd == "start":
                    def go():
                        self.manual_start = True
                        self.changed.set()
                    loop.call_soon_threadsafe(go)
                elif cmd == "status":
                    loop.call_soon_threadsafe(lambda: self.say(
                        f"phase={self.phase} players={[p.pid for p in self.players.values()]}"))
        threading.Thread(target=reader, daemon=True).start()

    async def serve(self):
        srv = await asyncio.start_server(self.handle_conn, self.a.host, self.a.port, limit=MAX_LINE)
        self.say(f"{PROTOCOL} 伺服器監聽 {self.a.host}:{self.a.port}（輸入 start 可提早開局）")
        self.start_console()
        played = 0
        async with srv:
            while self.a.games == 0 or played < self.a.games:
                await self.run_game()
                played += 1
                await asyncio.sleep(0.5)
                if self.logf:
                    self.logf.close()
                    self.logf = None
                await self.reap_bots()


# ---------------------------------------------------------------------------
# 客戶端（人類玩家與 AI 代理人共用骨架）
# ---------------------------------------------------------------------------
class Client:
    kind = "human"

    def __init__(self, args):
        self.a = args
        self.me = None
        self.secret = None
        self.salt = None
        self.players = {}
        self.order = []
        self.alive = []
        self.commits = {}
        self.records = {}
        self.cands = {}
        self.rules = {}
        self.finished = False
        self.task = None           # 目前進行中的互動工作
        self.task_turn = None
        self.wlock = asyncio.Lock()

    # ----- 輸出 -----
    def show(self, text):
        print(text, flush=True)

    def name(self, pid):
        p = self.players.get(pid)
        return f"{pid}({p['name']})" if p else pid

    async def send(self, msg):
        async with self.wlock:
            self.writer.write(encode(msg))
            await self.writer.drain()

    def spawn(self, coro, turn=None):
        if self.task and not self.task.done():
            self.task.cancel()
        self.task = asyncio.create_task(coro)
        self.task_turn = turn

    # ----- 主迴圈 -----
    async def run(self):
        self.reader, self.writer = await asyncio.open_connection(self.a.host, self.a.port, limit=1 << 20)
        await self.send({"type": "HELLO", "protocol": PROTOCOL, "name": self.a.name,
                         "team": self.a.team, "kind": self.kind, "software": SOFTWARE})
        self.on_start()
        try:
            while not self.finished:
                raw = await self.reader.readline()
                if not raw:
                    break
                msg, err = decode_line(raw)
                if msg is None:
                    continue
                await self.handle(msg)
        finally:
            if self.task and not self.task.done():
                self.task.cancel()
            self.writer.close()
        if not self.finished:
            self.show("與伺服器的連線已中斷。")

    def on_start(self):
        pass

    async def handle(self, m):
        t = m["type"]
        if t == "WELCOME":
            self.me = m["player_id"]
            self.show(f"已加入伺服器，你的編號是 {self.me}")
        elif t == "LOBBY":
            self.players = {p["id"]: p for p in m["players"]}
            names = "、".join(f"{p['id']}({p['name']})" for p in m["players"])
            self.show(f"[大廳] {len(m['players'])}/{m['max_players']}：{names}")
        elif t == "GAME_START":
            self.players = {p["id"]: p for p in m["players"]}
            self.rules = m["rules"]
            self.show(f"遊戲開始！順序：{' → '.join(self.name(x) for x in m['order'])}")
            self.spawn(self.do_commit())
        elif t == "COMMITS":
            self.order = m["order"]
            self.alive = list(self.order)
            self.commits = m["commits"]
            self.records = {pid: [] for pid in self.order}
            self.cands = {pid: list(ALL_NUMBERS) for pid in self.order if pid != self.me}
            self.show(f"所有玩家已送出承諾值，參賽者：{'、'.join(self.name(x) for x in self.order)}")
        elif t == "TURN":
            self.alive = m["alive"]
            if m["guesser"] == self.me:
                self.spawn(self.do_guess(m["turn_id"]), m["turn_id"])
            else:
                self.show(f"\n— 第 {m['turn_id']} 回合：等待 {self.name(m['guesser'])} 喊數 —")
        elif t == "GUESS_MADE":
            if self.me in m["responders"]:
                self.spawn(self.do_feedback(m["turn_id"], m["guesser"], m["guess"]), m["turn_id"])
            else:
                self.show(f"{self.name(m['guesser'])} 喊出 {m['guess']}，等待其他玩家回報")
        elif t == "TURN_RESULT":
            if self.task_turn == m["turn_id"] and self.task and not self.task.done():
                self.task.cancel()
            self.on_turn_result(m)
        elif t == "REVEAL_REQUEST":
            await self.send({"type": "REVEAL", "secret": self.secret, "salt": self.salt})
        elif t == "REVEALED":
            self.on_revealed(m)
        elif t == "GAME_OVER":
            self.on_game_over(m)
            self.finished = True
        elif t == "ERROR":
            self.show(f"[錯誤] {m.get('code')}：{m.get('message')}" + ("（致命）" if m.get("fatal") else ""))
        elif t == "PING":
            reply = {"type": "PONG"}
            if "nonce" in m:
                reply["nonce"] = m["nonce"]
            await self.send(reply)
        elif t == "CHAT":
            self.show(f"[聊天] {self.name(m.get('from'))}：{m.get('text')}")
        # 其他未知類型依協定規定忽略

    def on_turn_result(self, m):
        tid = m["turn_id"]
        if m["skipped"]:
            self.show(f"第 {tid} 回合：{self.name(m['guesser'])} 逾時未喊數，跳過")
        else:
            parts = []
            for r in m["results"]:
                pid, a, b = r["player"], r["a"], r["b"]
                self.records.setdefault(pid, []).append((tid, m["guess"], a, b))
                if pid in self.cands:
                    self.cands[pid] = [s for s in self.cands[pid] if score(m["guess"], s) == (a, b)]
                parts.append(f"{self.name(pid)} {a}A{b}B")
            self.show(f"第 {tid} 回合：{self.name(m['guesser'])} 喊 {m['guess']} → " + "，".join(parts))
        for key, label in (("eliminated", "被猜中淘汰"), ("forfeited", "棄權"), ("disqualified", "回報矛盾遭取消資格")):
            for pid in m[key]:
                self.show(f"  ✗ {self.name(pid)} {label}")
                if pid in self.alive:
                    self.alive.remove(pid)

    def on_revealed(self, m):
        pid = m["player"]
        mine, bad = verify_reveal(self.commits.get(pid), self.records.get(pid, []), m["secret"], m["salt"])
        note = "" if mine == m["verdict"] else f"（本地驗證為 {mine}，與伺服器判定不一致！）"
        self.show(f"  揭示 {self.name(pid)}：秘密數字 {m['secret']}，判定 {m['verdict']}{note}")

    def on_game_over(self, m):
        self.show(f"\n===== 遊戲結束（{m['reason']}，共 {m['turns']} 回合）=====")
        for row in m["ranking"]:
            rank = row["rank"] if row["rank"] is not None else "—"
            tag = " ← 你" if row["player"] == self.me else ""
            self.show(f"  名次 {rank}：{self.name(row['player'])}  {row['status']}{tag}")

    # ----- 由子類別實作 -----
    async def do_commit(self):
        raise NotImplementedError

    async def do_guess(self, turn_id):
        raise NotImplementedError

    async def do_feedback(self, turn_id, guesser, guess):
        raise NotImplementedError

    async def commit_secret(self, secret):
        self.secret = secret
        self.salt = secrets.token_hex(16)
        await self.send({"type": "COMMIT", "commit": make_commit(self.secret, self.salt)})


class HumanClient(Client):
    kind = "human"

    def on_start(self):
        loop = asyncio.get_running_loop()
        self.lines: asyncio.Queue = asyncio.Queue()
        self.interactive = False

        def reader():
            while True:
                line = sys.stdin.readline()
                loop.call_soon_threadsafe(self.on_line, line if line else None)
                if not line:
                    break
        threading.Thread(target=reader, daemon=True).start()

    def on_line(self, line):
        if line is None:
            return
        s = line.strip()
        if s.startswith("/"):
            cmd, _, rest = s.partition(" ")
            if cmd == "/say" and rest:
                asyncio.create_task(self.send({"type": "CHAT", "text": rest[:200]}))
            elif cmd == "/quit":
                asyncio.create_task(self.send({"type": "BYE"}))
            elif cmd == "/cands":
                self.show("候選數量：" + "，".join(f"{self.name(p)}={len(c)}" for p, c in self.cands.items()
                                               if p in self.alive))
            else:
                self.show("指令：/say 文字、/cands、/quit")
        elif self.interactive:
            self.lines.put_nowait(s)       # 互動進行中：依序交給提示使用（允許預先輸入）
        else:
            self.show("（目前不需要輸入；可用 /say 聊天）")

    def begin(self):
        """開始一段互動：丟棄先前殘留的輸入。"""
        while not self.lines.empty():
            self.lines.get_nowait()
        self.interactive = True

    async def ask(self, text, deadline):
        loop = asyncio.get_running_loop()
        print(text, end="", flush=True)
        try:
            return await asyncio.wait_for(self.lines.get(), max(0.1, deadline - loop.time()))
        except asyncio.TimeoutError:
            self.show("\n（輸入逾時）")
            return None

    async def do_commit(self):
        self.begin()
        try:
            await self._commit()
        finally:
            self.interactive = False

    async def do_guess(self, turn_id):
        self.begin()
        try:
            await self._guess(turn_id)
        finally:
            self.interactive = False

    async def do_feedback(self, turn_id, guesser, guess):
        self.begin()
        try:
            await self._feedback(turn_id, guesser, guess)
        finally:
            self.interactive = False

    async def _commit(self):
        loop = asyncio.get_running_loop()
        deadline = loop.time() + self.rules["commit_timeout"] - 2
        while True:
            s = await self.ask("請設定秘密數字（四位互異數字，可含 0；直接 Enter 隨機產生）：", deadline)
            if s is None or s == "":
                s = random.choice(ALL_NUMBERS)
                self.show(f"已隨機產生秘密數字 {s}")
            if valid_number(s):
                break
            self.show("格式不符，請重新輸入。")
        await self.commit_secret(s)
        self.show(f"你的秘密數字是 {s}（已送出承諾值，數字本身不會傳出）")

    async def _guess(self, turn_id):
        loop = asyncio.get_running_loop()
        deadline = loop.time() + self.rules["guess_timeout"] - 1
        hint = "，".join(f"{self.name(p)} 剩 {len(self.cands[p])}" for p in self.alive if p in self.cands)
        self.show(f"\n— 第 {turn_id} 回合：輪到你喊數！（候選數：{hint}）")
        while True:
            s = await self.ask("請輸入四位互異數字：", deadline)
            if s is None:
                return
            if valid_number(s):
                await self.send({"type": "GUESS", "turn_id": turn_id, "guess": s})
                return
            self.show("格式不符，請重新輸入。")

    async def _feedback(self, turn_id, guesser, guess):
        loop = asyncio.get_running_loop()
        deadline = loop.time() + self.rules["feedback_timeout"] - 1
        a0, b0 = score(guess, self.secret)
        while True:
            s = await self.ask(f"{self.name(guesser)} 喊 {guess}，你的秘密 {self.secret}。"
                               f"請輸入幾A幾B（Enter 送出 {a0}A{b0}B）：", deadline)
            if s is None:
                return
            if s == "":
                a, b = a0, b0
            else:
                mt = re.fullmatch(r"\s*([0-4])\s*[Aa]?\s*[, ]?\s*([0-4])\s*[Bb]?\s*", s)
                if not mt or (int(mt.group(1)), int(mt.group(2))) not in VALID_FEEDBACK:
                    self.show("格式不符或組合不可能（例：1A2B、1 2）。")
                    continue
                a, b = int(mt.group(1)), int(mt.group(2))
                if (a, b) != (a0, b0):
                    c = await self.ask(f"注意：實際比對結果為 {a0}A{b0}B，不實回報將在終局驗證時被取消資格。"
                                       f"仍要送出 {a}A{b}B？(y/N)：", deadline)
                    if c is None or c.lower() != "y":
                        continue
            await self.send({"type": "FEEDBACK", "turn_id": turn_id, "a": a, "b": b})
            return


class AIClient(Client):
    kind = "ai"

    def show(self, text):
        if not self.a.quiet:
            print(f"[{self.a.name}] {text}", flush=True)

    async def do_commit(self):
        await self.commit_secret(random.choice(ALL_NUMBERS))

    async def do_feedback(self, turn_id, guesser, guess):
        a, b = score(guess, self.secret)
        await self.send({"type": "FEEDBACK", "turn_id": turn_id, "a": a, "b": b})

    async def do_guess(self, turn_id):
        guess = await asyncio.to_thread(self.choose_guess)
        await self.send({"type": "GUESS", "turn_id": turn_id, "guess": guess})

    def choose_guess(self):
        """基準策略：鎖定候選最少的對手，於其候選中挑選能把候選切成最多組的數字（most-parts）。"""
        opps = [p for p in self.alive if p != self.me and p in self.cands]
        target = min(opps, key=lambda p: len(self.cands[p]))
        C = self.cands[target]
        if not C:
            return random.choice(ALL_NUMBERS)
        if len(C) <= 2 or len(C) > 2000:
            return random.choice(C)
        pool = C if len(C) <= 150 else random.sample(C, 150)
        sample = C if len(C) <= 500 else random.sample(C, 500)
        return max(pool, key=lambda g: len({score(g, s) for s in sample}))


# ---------------------------------------------------------------------------
# 命令列
# ---------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser(description="BC/1.0 幾A幾B 多人對戰（參考原型）")
    sub = ap.add_subparsers(dest="role", required=True)
    s = sub.add_parser("server", help="以莊家（伺服器）身分執行")
    s.add_argument("--host", default="0.0.0.0")
    s.add_argument("--port", type=int, default=DEFAULT_PORT)
    s.add_argument("--players", type=int, default=2, help="本局玩家總數（2–6，含 AI）")
    s.add_argument("--bots", type=int, default=0, help="由伺服器自動啟動的 AI 玩家數")
    s.add_argument("--bot-cmd", default=None, help="啟動外部 AI 的命令樣板，可用 {host} {port} {name}")
    s.add_argument("--guess-timeout", type=float, default=60)
    s.add_argument("--feedback-timeout", type=float, default=60)
    s.add_argument("--commit-timeout", type=float, default=30)
    s.add_argument("--reveal-timeout", type=float, default=15)
    s.add_argument("--max-turns", type=int, default=120)
    s.add_argument("--max-skips", type=int, default=3)
    s.add_argument("--games", type=int, default=1, help="連續舉辦的局數，0 表示不限")
    s.add_argument("--log-dir", default="logs")
    for role in ("client", "ai"):
        c = sub.add_parser(role, help="以人類玩家客戶端執行" if role == "client" else "以 AI 代理人執行")
        c.add_argument("--host", required=True)
        c.add_argument("--port", type=int, default=DEFAULT_PORT)
        c.add_argument("--name", required=True)
        c.add_argument("--team", default="G00")
        if role == "ai":
            c.add_argument("--quiet", action="store_true")
    args = ap.parse_args()
    if args.role == "server":
        if not 2 <= args.players <= 6:
            ap.error("--players 必須介於 2 與 6")
        if not 0 <= args.bots <= args.players:
            ap.error("--bots 必須介於 0 與 --players")
        asyncio.run(Server(args).serve())
    elif args.role == "client":
        asyncio.run(HumanClient(args).run())
    else:
        asyncio.run(AIClient(args).run())


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        pass
