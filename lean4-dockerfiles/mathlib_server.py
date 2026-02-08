#!/usr/bin/env python3
"""Lean 4 + Mathlib HTTP server.

Like lean_server.py but uses `lake env lean <file>` so that Mathlib imports work.
Code is written to /project/MathProject.lean before each run.
"""

import http.server
import json
import os
import subprocess
import time

PROJECT_DIR = "/project"
SOURCE_FILE = os.path.join(PROJECT_DIR, "MathProject.lean")
DEFAULT_TIMEOUT = int(os.environ.get("LEAN_TIMEOUT", "60"))


class MathLibHandler(http.server.BaseHTTPRequestHandler):
    server_version = "MathLibServer/0.1"

    def do_POST(self):
        content_length = int(self.headers.get("Content-Length", "0"))
        body = self.rfile.read(content_length).decode("utf-8")
        timeout = DEFAULT_TIMEOUT
        if self.headers.get("X-Lean-Timeout"):
            try:
                timeout = int(self.headers["X-Lean-Timeout"])
            except ValueError:
                pass

        result = run_lean(body, timeout)
        payload = json.dumps(result).encode("utf-8")
        status = 200 if result["ok"] else 400
        if result["exitCode"] == -1:  # timeout
            status = 408

        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(payload)))
        self.end_headers()
        self.wfile.write(payload)

    def do_GET(self):
        if self.path == "/health":
            result = subprocess.run(
                ["lean", "--version"],
                capture_output=True, text=True, timeout=10,
                cwd=PROJECT_DIR,
            )
            body = {"version": result.stdout.strip(), "mathlib": True}
            payload = json.dumps(body).encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            self.send_header("Content-Length", str(len(payload)))
            self.end_headers()
            self.wfile.write(payload)
            return

        self.send_response(405)
        self.send_header("Allow", "POST")
        self.end_headers()

    def log_message(self, format, *args):
        if os.environ.get("LEAN_SERVER_QUIET"):
            return
        super().log_message(format, *args)


def run_lean(code, timeout):
    # Write code to the project source file
    with open(SOURCE_FILE, "w") as f:
        f.write(code)

    start = time.monotonic()
    try:
        result = subprocess.run(
            ["lake", "env", "lean", SOURCE_FILE],
            text=True,
            capture_output=True,
            timeout=timeout,
            cwd=PROJECT_DIR,
        )
        elapsed = round(time.monotonic() - start, 3)
        return {
            "ok": result.returncode == 0,
            "stdout": result.stdout,
            "stderr": result.stderr,
            "exitCode": result.returncode,
            "elapsed": elapsed,
        }
    except subprocess.TimeoutExpired:
        elapsed = round(time.monotonic() - start, 3)
        return {
            "ok": False,
            "stdout": "",
            "stderr": f"Lean process timed out after {timeout}s",
            "exitCode": -1,
            "elapsed": elapsed,
        }


def main():
    host = os.environ.get("LEAN_SERVER_HOST", "0.0.0.0")
    port = int(os.environ.get("LEAN_SERVER_PORT", "8000"))
    server = http.server.ThreadingHTTPServer((host, port), MathLibHandler)
    print(f"Mathlib server listening on http://{host}:{port}")
    print(f"  POST /       — evaluate Lean code (with Mathlib)")
    print(f"  GET  /health — health check")
    print(f"  Timeout: {DEFAULT_TIMEOUT}s")
    print(f"  Project dir: {PROJECT_DIR}")
    server.serve_forever()


if __name__ == "__main__":
    main()
