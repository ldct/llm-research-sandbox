#!/usr/bin/env python3
"""Simple GAP command server.

POST body should contain GAP commands. The server responds with the
stdout/stderr from the GAP invocation.
"""

from __future__ import annotations

import http.server
import os
import subprocess
from pathlib import Path
from typing import Tuple

GAP_ROOT = Path(__file__).resolve().parent / "gap-src" / "gap-4.15.1"
GAP_BIN = GAP_ROOT / "gap"


class GapHandler(http.server.BaseHTTPRequestHandler):
    server_version = "GapServer/0.1"

    def do_POST(self) -> None:  # noqa: N802
        content_length = int(self.headers.get("Content-Length", "0"))
        body = self.rfile.read(content_length).decode("utf-8")
        output, status = run_gap(body)

        payload = output.encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "text/plain; charset=utf-8")
        self.send_header("Content-Length", str(len(payload)))
        self.end_headers()
        self.wfile.write(payload)

    def do_GET(self) -> None:  # noqa: N802
        self.send_response(405)
        self.send_header("Allow", "POST")
        self.end_headers()

    def log_message(self, format: str, *args: object) -> None:  # noqa: A003
        if os.environ.get("GAP_SERVER_QUIET"):
            return
        super().log_message(format, *args)


def run_gap(commands: str) -> Tuple[str, int]:
    if not GAP_BIN.exists():
        return "GAP binary not found. Build GAP first.\n", 500

    input_data = commands.rstrip()
    if input_data:
        input_data += "\n"
    input_data += "QUIT;\n"

    result = subprocess.run(
        [str(GAP_BIN), "-q"],
        input=input_data,
        text=True,
        capture_output=True,
        cwd=str(GAP_ROOT),
        check=False,
    )

    output = result.stdout
    if result.stderr:
        output = f"{output}{result.stderr}"

    status = 200 if result.returncode == 0 else 500
    return output, status


def main() -> None:
    host = os.environ.get("GAP_SERVER_HOST", "0.0.0.0")
    port = int(os.environ.get("GAP_SERVER_PORT", "8000"))
    server = http.server.ThreadingHTTPServer((host, port), GapHandler)
    print(f"Serving GAP commands on http://{host}:{port}")
    server.serve_forever()


if __name__ == "__main__":
    main()
