#!/usr/bin/env python3
"""Lean 4 + Mathlib REPL HTTP server.

Spawns a persistent lean-repl process, imports Mathlib once at startup,
then serves requests by sending commands to the REPL via stdin/stdout JSON.
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
DEFAULT_TIMEOUT = int(os.environ.get("LEAN_TIMEOUT", "120"))


class ReplProcess:
    """Manages a persistent lean-repl subprocess."""

    def __init__(self):
        self.proc = None
        self.lock = threading.Lock()
        self.base_env = None  # env number after `import Mathlib`
        self.ready = False
        self.starting = False
        self.start_error = None

    def start(self):
        """Spawn the REPL process and import Mathlib."""
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
            print("[repl] Process started, importing Mathlib...", flush=True)
            t0 = time.monotonic()
            resp = self._send_raw('{"cmd": "import Mathlib"}')
            elapsed = time.monotonic() - t0
            if resp is None:
                self.start_error = "REPL did not respond to import Mathlib"
                print(f"[repl] ERROR: {self.start_error}", flush=True)
                return
            if "env" not in resp:
                self.start_error = f"Unexpected response: {resp}"
                print(f"[repl] ERROR: {self.start_error}", flush=True)
                return
            self.base_env = resp["env"]
            self.ready = True
            print(f"[repl] Mathlib imported in {elapsed:.1f}s (env={self.base_env})", flush=True)
        except Exception as e:
            self.start_error = str(e)
            print(f"[repl] ERROR starting: {e}", flush=True)
        finally:
            self.starting = False

    def _send_raw(self, cmd_json):
        """Send a JSON command to the REPL and read one JSON response.
        Commands are separated by blank lines. The REPL outputs multi-line
        pretty-printed JSON followed by a blank line."""
        if self.proc is None or self.proc.poll() is not None:
            return None
        try:
            payload = cmd_json.encode() + b"\n\n"
            self.proc.stdin.write(payload)
            self.proc.stdin.flush()
            # Accumulate lines until we get valid JSON
            buf = ""
            while True:
                line = self.proc.stdout.readline()
                if not line:
                    # EOF — process died
                    return None
                text = line.decode()
                # Blank line = separator between responses
                if text.strip() == "" and buf.strip():
                    try:
                        return json.loads(buf)
                    except json.JSONDecodeError:
                        # Not complete yet, keep reading
                        buf += text
                        continue
                buf += text
        except Exception as e:
            print(f"[repl] _send_raw error: {e}", flush=True)
            return None

    def send_command(self, code, timeout=None):
        """Send user code to the REPL using the base Mathlib env.
        Returns (response_dict, elapsed_seconds) or (None, elapsed)."""
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


# Global REPL instance
repl = ReplProcess()


class ReplHandler(http.server.BaseHTTPRequestHandler):
    server_version = "MathLibReplServer/0.1"

    def do_POST(self):
        if not repl.ready:
            self._json_response(503, {
                "ok": False,
                "error": "REPL not ready (still importing Mathlib)" if repl.starting
                         else f"REPL not ready: {repl.start_error}",
            })
            return

        content_length = int(self.headers.get("Content-Length", "0"))
        body = self.rfile.read(content_length).decode("utf-8")

        resp, elapsed = repl.send_command(body)

        if resp is None:
            # REPL died — try restart in background
            threading.Thread(target=repl.restart, daemon=True).start()
            self._json_response(502, {
                "ok": False,
                "error": "REPL process crashed, restarting",
                "elapsed": elapsed,
            })
            return

        # Translate REPL response to API format
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
            }
            if repl.starting:
                body["status"] = "importing Mathlib"
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

    # Start REPL + import Mathlib in background so health endpoint is available immediately
    threading.Thread(target=repl.start, daemon=True).start()

    server = http.server.ThreadingHTTPServer((host, port), ReplHandler)
    print(f"REPL server listening on http://{host}:{port}", flush=True)
    print(f"  POST /       — evaluate Lean code (with Mathlib)", flush=True)
    print(f"  GET  /health — health check", flush=True)
    print(f"  Mathlib import running in background...", flush=True)
    server.serve_forever()


if __name__ == "__main__":
    main()
