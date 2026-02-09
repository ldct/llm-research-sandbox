# Mathlib REPL Server — Plan

## Problem

The current mathlib server (`mathlib_server.py`) spawns a fresh `lake env lean <file>`
for every request. Each invocation re-loads oleans from disk:

| Scenario                    | Time    |
|-----------------------------|---------|
| Targeted import (hot)       | ~3s     |
| Targeted import (cold)      | ~23s    |
| Full `import Mathlib` (hot) | ~75s    |
| Full `import Mathlib` (cold)| ~83s    |

The bottleneck is Lean reading ~5.2GB of olean/private/ilean/ir/server files
from disk on every invocation. There is no cross-invocation caching.

## Solution: lean-repl with persistent process

[lean-repl](https://github.com/leanprover-community/repl) is a REPL for Lean 4
that communicates via JSON on stdin/stdout. Key features:

1. **Persistent process** — one long-lived REPL process handles multiple requests
2. **Environment reuse** — each response returns an `env` number; subsequent
   commands can reference it to run in that environment
3. **Import once** — `import Mathlib` runs once at startup; all subsequent
   requests reuse that loaded environment

### Architecture

```
┌──────────────────────────────────────────────────────┐
│  Container                                           │
│                                                      │
│  ┌──────────────────┐     ┌─────────────────────┐    │
│  │ repl_server.py   │────▸│ lake env repl       │    │
│  │ (HTTP server)    │◂────│ (persistent process) │    │
│  │ port 8000        │     │ stdin/stdout JSON    │    │
│  └──────────────────┘     └─────────────────────┘    │
│         │                                            │
└─────────┼────────────────────────────────────────────┘
          │
     HTTP requests
```

### Startup sequence

1. Container starts `repl_server.py`
2. Server spawns `lake env /opt/repl/.lake/build/bin/repl` as a subprocess
   (stdin/stdout pipes)
3. Server sends `{"cmd": "import Mathlib"}` to the REPL
4. REPL loads all Mathlib oleans and responds with `{"env": 0}` — this
   takes ~22s (hot disk) to ~75s (cold disk), but only happens once
5. Server stores `env: 0` as the base Mathlib environment
6. Server is now ready to accept HTTP requests

### Request handling

1. HTTP POST arrives with Lean code (e.g. `#check Real.sqrt`)
2. Server sends `{"cmd": "<code>", "env": 0}` to the REPL process
   (always using env 0 = the base Mathlib environment)
3. REPL evaluates and returns JSON with messages, sorries, new env number
4. Server translates REPL response to the API format:
   ```json
   {
     "ok": true/false,
     "messages": [{"severity": "...", "pos": {...}, "data": "..."}],
     "sorries": [...],
     "env": <n>,
     "elapsed": 0.5
   }
   ```
5. Note: we always reset to env 0 for independent requests.
   A future enhancement could support stateful sessions via the `env` field.

### Why this is fast

- **Import once** — Mathlib oleans are loaded into the REPL process memory
  once at startup. All subsequent requests skip the import entirely.
- **Persistent process** — no subprocess spawn overhead per request
- **Environment forking** — each request starts from the base env (env 0)
  without copying; the REPL manages environments as incremental snapshots

## Build steps

### 1. Dockerfile.mathlib4-repl

Based on `ghcr.io/ldct/mathlib4:v4.27.0`.

```dockerfile
FROM ghcr.io/ldct/mathlib4:v4.27.0

# Install python3 and git
RUN apt-get update && apt-get install -y python3 git && rm -rf /var/lib/apt/lists/*

# Clone and build lean-repl (matching Lean version)
RUN cd /opt && \
    git clone --branch v4.27.0 --depth 1 \
      https://github.com/leanprover-community/repl.git && \
    cd repl && lake build repl

COPY repl_server.py /repl_server.py

EXPOSE 8000
CMD ["python3", "/repl_server.py"]
```

### 2. repl_server.py

Python HTTP server that:
- On startup, spawns `lake env /opt/repl/.lake/build/bin/repl` in `/project`
- Sends `{"cmd": "import Mathlib"}` and waits for the env response
  (this is the slow one-time cost; server reports "not ready" until done)
- Handles POST requests by sending `{"cmd": ..., "env": 0}` to REPL
- Reads JSON response from REPL stdout
- Translates to API response format
- Handles REPL process crashes with automatic restart + re-import
- Serializes requests (single REPL process, one at a time)

Key implementation details:
- Use `subprocess.Popen` with `stdin=PIPE, stdout=PIPE`
- Read responses by looking for complete JSON objects (one per line)
- Commands separated by blank lines (write `json + "\n\n"`)
- Thread lock to serialize access to the REPL process
- Health endpoint returns `{"ready": false}` while Mathlib is importing,
  `{"ready": true}` once env 0 is available

### 3. Cloudflare deployment

- Push new image as `mathlib4-repl-server:v4.27.0`
- Add new container class `Mathlib4v27ReplContainer` in wrangler.jsonc
- Add new route `mathlib-repl-4-27-0` in Worker
- Keep existing `mathlib-4-27-0` endpoint as fallback
- Instance type: `standard-3` (16GB disk for 10GB image)
- Sleep timeout: `300s` (longer, since startup cost is high and we want
  to amortize the one-time import across many requests)

## Expected performance

| Scenario                     | Current  | With REPL  |
|------------------------------|----------|------------|
| Container cold start + ready | ~2s      | ~2s + 22-75s (one-time import) |
| Subsequent `#check Real.sqrt`| ~75s     | <1s |
| Subsequent `#eval` (simple)  | ~3s      | <1s |
| Prove a Mathlib theorem      | ~20s     | ~1-5s (just tactic execution) |

The massive improvement is that **Mathlib is already loaded** in the REPL
process. Each request only needs to type-check/evaluate the user's code,
not re-import thousands of modules.

## Risks & mitigations

1. **REPL process memory** — full Mathlib environment in memory could be
   several GB. Standard-3 has 4GB RAM.
   Mitigation: measure actual RSS. If too large, use targeted imports
   instead of full `import Mathlib`.

2. **REPL process memory leak** — long-lived process may accumulate state
   from user commands (each `env` keeps references).
   Mitigation: restart REPL after N requests or if memory exceeds threshold.

3. **REPL crash on bad input** — malicious code could crash the REPL.
   Mitigation: catch crashes, auto-restart with re-import, return error.

4. **Concurrency** — single REPL process is single-threaded.
   Mitigation: serialize requests with a lock. Cloudflare can scale out
   with multiple container instances.

5. **Startup latency** — first request must wait for `import Mathlib` to
   finish (~22-75s depending on disk cache).
   Mitigation: health endpoint reports readiness; Worker can return
   "warming up" response. Container sleep timeout set to 300s to keep
   the process alive longer.

6. **lean-repl v4.27.0 compat** — need to verify the repl builds against
   the mathlib project's Lean toolchain.
   Mitigation: there's a tagged release `v4.27.0` of lean-repl.

## Files to create

1. `lean4-dockerfiles/Dockerfile.mathlib4-repl` — Docker build
2. `lean4-dockerfiles/repl_server.py` — HTTP ↔ REPL bridge
3. `lean4-server-cf/wrangler.jsonc` — add container + route
4. `lean4-server-cf/src/index.ts` — add route handling

## Testing plan

1. Build Docker image locally
2. Test REPL manually: `docker run --rm -it <image> bash -c 'cd /project && lake env /opt/repl/.lake/build/bin/repl'`
3. Send `{"cmd": "import Mathlib"}`, then `{"cmd": "#check Real.sqrt", "env": 0}`
4. Test HTTP server: health check, wait for ready, simple eval, Mathlib theorem
5. Measure startup import time and per-request latency
6. Push to Cloudflare and test end-to-end
