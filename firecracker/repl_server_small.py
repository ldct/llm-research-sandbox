#!/usr/bin/env python3
import http.server, json, os, subprocess, sys, threading, time

PROJECT_DIR = "/project"
REPL_BIN = "/opt/repl/.lake/build/bin/repl"

class ReplProcess:
    def __init__(self):
        self.proc = None
        self.lock = threading.Lock()
        self.base_env = None
        self.ready = False
        self.starting = False
        self.start_error = None

    def start(self):
        self.starting = True
        self.ready = False
        try:
            self.proc = subprocess.Popen(
                ["lake", "env", REPL_BIN],
                stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                cwd=PROJECT_DIR)
            print("[repl] Importing Mathlib.Data.Nat.Basic...", flush=True)
            t0 = time.monotonic()
            resp = self._send_raw('{"cmd": "import Mathlib.Data.Nat.Basic"}')
            elapsed = time.monotonic() - t0
            if resp and "env" in resp:
                self.base_env = resp["env"]
                self.ready = True
                print(f"[repl] Imported in {elapsed:.1f}s (env={self.base_env})", flush=True)
            else:
                self.start_error = f"Failed: {resp}"
                print(f"[repl] ERROR: {self.start_error}", flush=True)
        except Exception as e:
            self.start_error = str(e)
        finally:
            self.starting = False

    def _send_raw(self, cmd_json):
        if self.proc is None or self.proc.poll() is not None:
            return None
        try:
            self.proc.stdin.write(cmd_json.encode() + b"\n\n")
            self.proc.stdin.flush()
            buf = ""
            while True:
                line = self.proc.stdout.readline()
                if not line: return None
                text = line.decode()
                if text.strip() == "" and buf.strip():
                    try: return json.loads(buf)
                    except json.JSONDecodeError: buf += text; continue
                buf += text
        except: return None

    def send_command(self, code):
        if not self.ready: return None, 0
        with self.lock:
            t0 = time.monotonic()
            resp = self._send_raw(json.dumps({"cmd": code, "env": self.base_env}))
            return resp, round(time.monotonic() - t0, 3)

repl = ReplProcess()

class Handler(http.server.BaseHTTPRequestHandler):
    def do_POST(self):
        if not repl.ready:
            self._json(503, {"ok": False, "error": "not ready"})
            return
        body = self.rfile.read(int(self.headers.get("Content-Length", "0"))).decode()
        resp, elapsed = repl.send_command(body)
        if resp is None:
            self._json(502, {"ok": False, "error": "crashed"})
            return
        msgs = resp.get("messages", [])
        ok = not any(m.get("severity") == "error" for m in msgs)
        self._json(200 if ok else 400, {"ok": ok, "messages": msgs, "elapsed": elapsed})

    def do_GET(self):
        self._json(200, {"ready": repl.ready, "base_env": repl.base_env})

    def _json(self, code, body):
        data = json.dumps(body).encode()
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def log_message(self, *a): pass

threading.Thread(target=repl.start, daemon=True).start()
server = http.server.ThreadingHTTPServer(("0.0.0.0", 8000), Handler)
print("Server on :8000", flush=True)
server.serve_forever()
