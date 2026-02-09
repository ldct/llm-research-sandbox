#!/usr/bin/env python3
"""Generate a pickled Mathlib environment.

Runs inside the Docker build to:
1. Start the REPL
2. Import Mathlib
3. Pickle the resulting environment to /data/mathlib.pickle
"""

import json
import subprocess
import sys
import time

PROJECT_DIR = "/project"
REPL_BIN = "/opt/repl/.lake/build/bin/repl"
PICKLE_PATH = "/data/mathlib.pickle"


def send_raw(proc, cmd_json):
    """Send a JSON command and read one JSON response."""
    payload = cmd_json.encode() + b"\n\n"
    proc.stdin.write(payload)
    proc.stdin.flush()
    buf = ""
    while True:
        line = proc.stdout.readline()
        if not line:
            # Check stderr
            err = proc.stderr.read().decode() if proc.stderr else ""
            print(f"[pickle] REPL EOF. stderr: {err}", flush=True)
            return None
        text = line.decode()
        if text.strip() == "" and buf.strip():
            try:
                return json.loads(buf)
            except json.JSONDecodeError:
                buf += text
                continue
        buf += text


def main():
    print(f"[pickle] Starting REPL: lake env {REPL_BIN}", flush=True)
    proc = subprocess.Popen(
        ["lake", "env", REPL_BIN],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        cwd=PROJECT_DIR,
    )

    # Step 1: Import Mathlib
    print("[pickle] Importing Mathlib...", flush=True)
    t0 = time.monotonic()
    resp = send_raw(proc, '{"cmd": "import Mathlib"}')
    elapsed = time.monotonic() - t0
    if resp is None or "env" not in resp:
        print(f"[pickle] FAILED to import Mathlib: {resp}", flush=True)
        sys.exit(1)
    env_id = resp["env"]
    print(f"[pickle] Mathlib imported in {elapsed:.1f}s (env={env_id})", flush=True)

    # Step 2: Pickle the environment
    print(f"[pickle] Pickling env {env_id} to {PICKLE_PATH}...", flush=True)
    t0 = time.monotonic()
    cmd = json.dumps({"env": env_id, "pickleTo": PICKLE_PATH})
    resp = send_raw(proc, cmd)
    elapsed = time.monotonic() - t0
    print(f"[pickle] Pickle response in {elapsed:.1f}s: {resp}", flush=True)

    proc.stdin.close()
    proc.wait(timeout=10)

    # Check file size
    import os
    size_mb = os.path.getsize(PICKLE_PATH) / (1024 * 1024)
    print(f"[pickle] Pickle file: {PICKLE_PATH} ({size_mb:.1f} MB)", flush=True)
    print("[pickle] Done!", flush=True)


if __name__ == "__main__":
    main()
