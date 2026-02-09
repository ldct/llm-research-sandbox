#!/usr/bin/env python3
"""Lean 4 + Mathlib REPL HTTP server with pickle support.

If a pickled environment exists at /data/mathlib.pickle, unpickles it
instead of running `import Mathlib` from scratch.
"""

import http.server
import json
import os
import subprocess
import sys
import threading
import time

PROJECT_DIR = "/project"
REPL_BIN = "/opt/repl/.lake/build/bin/repl"
PICKLE_PATH = "/data/mathlib.pickle"
DEFAULT_TIMEOUT = int(os.environ.get("LEAN_TIMEOUT", "120"))


class ReplProcess:
    """Manages a persistent lean-repl subprocess."""

    def __init__(self):
        self.proc = None
        self.lock = threading.Lock()
        self.base_env = None
        self.ready = False
        self.starting = False
        self.start_error = None

    def start(self):
        """Spawn the REPL process and load Mathlib (pickle or import)."""
        self.starting = True
        self.ready = False
        self.start_error = None
        try:
            print(f"[repl] Spawning: lake env {REPL_BIN}", flush=True)
            self.proc = subprocess.Popen(
                ["lake", "env", REPL_BIN],
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                cwd=PROJECT_DIR,
            )

            use_pickle = os.path.exists(PICKLE_PATH)
            if use_pickle:
                print(f"[repl] Unpickling Mathlib from {PICKLE_PATH}...", flush=True)
                cmd = json.dumps({"unpickleEnvFrom": PICKLE_PATH})
            else:
                print("[repl] No pickle found, importing Mathlib...", flush=True)
                cmd = '{"cmd": "import Mathlib"}'

            t0 = time.monotonic()
            resp = self._send_raw(cmd)
            elapsed = time.monotonic() - t0

            if resp is None:
                self.start_error = "REPL did not respond"
                print(f"[repl] ERROR: {self.start_error}", flush=True)
                return
            if "env" not in resp:
                self.start_error = f"Unexpected response: {resp}"
                print(f"[repl] ERROR: {self.start_error}", flush=True)
                return
            self.base_env = resp["env"]
            method = "unpickle" if use_pickle else "import"
            self.ready = True
            print(f"[repl] Mathlib loaded via {method} in {elapsed:.1f}s (env={self.base_env})", flush=True)
        except Exception as e:
            self.start_error = str(e)
            print(f"[repl] ERROR starting: {e}", flush=True)
        finally:
            self.starting = False

    def _send_raw(self, cmd_json):
        """Send a JSON command to the REPL and read one JSON response."""
        if self.proc is None or self.proc.poll() is not None:
            return None
        try:
            payload = cmd_json.encode() + b"\n\n"
            self.proc.stdin.write(payload)
            self.proc.stdin.flush()
            buf = ""
            while True:
                line = self.proc.stdout.readline()
                if not line:
                    return None
                text = line.decode()
                if text.strip() == "" and buf.strip():
                    try:
                        return json.loads(buf)
                    except json.JSONDecodeError:
                        buf += text
                        continue
                buf += text
        except Exception as e:
            print(f"[repl] _send_raw error: {e}", flush=True)
            return None

    def send_command(self, code, timeout=None):
        """Send user code to the REPL using the base Mathlib env."""
        if not self.ready:
            return None, 0
        with self.lock:
            cmd = json.dumps({"cmd": code, "env": self.base_env})
            t0 = time.monotonic()
            resp = self._send_raw(cmd)
            elapsed = round(time.monotonic() - t0, 3)
            if resp is None and self.proc and self.proc.poll() is not None:
                print("[repl] Process died, marking not ready", flush=True)
                self.ready = False
            return resp, elapsed

    def pickle_env(self, path):
        """Pickle the base environment to a file."""
        if not self.ready:
            return None
        with self.lock:
            cmd = json.dumps({"env": self.base_env, "pickleTo": path})
            return self._send_raw(cmd)

    def is_alive(self):
        return self.proc is not None and self.proc.poll() is None

    def restart(self):
        """Kill and restart the REPL process."""
        print("[repl] Restarting...", flush=True)
        if self.proc:
            try:
                self.proc.kill()
                self.proc.wait(timeout=5)
            except Exception:
                pass
        self.proc = None
        self.ready = False
        self.base_env = None
        self.start()


repl = ReplProcess()


class ReplHandler(http.server.BaseHTTPRequestHandler):
    server_version = "MathLibReplServer/0.2-pickle"

    def do_POST(self):
        if not repl.ready:
            self._json_response(503, {
                "ok": False,
                "error": "REPL not ready (still loading Mathlib)" if repl.starting
                         else f"REPL not ready: {repl.start_error}",
            })
            return

        content_length = int(self.headers.get("Content-Length", "0"))
        body = self.rfile.read(content_length).decode("utf-8")

        resp, elapsed = repl.send_command(body)

        if resp is None:
            threading.Thread(target=repl.restart, daemon=True).start()
            self._json_response(502, {
                "ok": False,
                "error": "REPL process crashed, restarting",
                "elapsed": elapsed,
            })
            return

        messages = resp.get("messages", [])
        sorries = resp.get("sorries", [])
        has_error = any(m.get("severity") == "error" for m in messages)
        ok = not has_error

        result = {
            "ok": ok,
            "messages": messages,
            "sorries": sorries,
            "env": resp.get("env"),
            "elapsed": elapsed,
        }

        self._json_response(200 if ok else 400, result)

    def do_GET(self):
        if self.path == "/health":
            alive = repl.is_alive()
            body = {
                "ready": repl.ready,
                "alive": alive,
                "mathlib": True,
                "repl": True,
                "base_env": repl.base_env,
                "pickle": os.path.exists(PICKLE_PATH),
            }
            if repl.starting:
                body["status"] = "loading Mathlib"
            elif repl.ready:
                body["status"] = "ready"
            else:
                body["status"] = f"error: {repl.start_error}"
            self._json_response(200, body)
            return

        self.send_response(405)
        self.send_header("Allow", "POST")
        self.end_headers()

    def _json_response(self, status, body):
        payload = json.dumps(body).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(payload)))
        self.end_headers()
        self.wfile.write(payload)

    def log_message(self, format, *args):
        if os.environ.get("LEAN_SERVER_QUIET"):
            return
        super().log_message(format, *args)


def main():
    host = os.environ.get("LEAN_SERVER_HOST", "0.0.0.0")
    port = int(os.environ.get("LEAN_SERVER_PORT", "8000"))

    threading.Thread(target=repl.start, daemon=True).start()

    server = http.server.ThreadingHTTPServer((host, port), ReplHandler)
    print(f"REPL server listening on http://{host}:{port}", flush=True)
    print(f"  POST /       — evaluate Lean code (with Mathlib)", flush=True)
    print(f"  GET  /health — health check", flush=True)
    print(f"  Mathlib loading in background...", flush=True)
    server.serve_forever()


if __name__ == "__main__":
    main()
