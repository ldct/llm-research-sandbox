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

## Solution: lean-repl with pre-pickled Mathlib environment

[lean-repl](https://github.com/leanprover-community/repl) is a REPL for Lean 4
that communicates via JSON on stdin/stdout. Key features:

1. **Persistent process** — one long-lived REPL process handles multiple requests
2. **Environment reuse** — each response returns an `env` number; subsequent
   commands can reference it to run in that environment
3. **Pickling** — environments can be serialized to `.olean` files and unpickled
   in new sessions, using memory mapping for fast loading

### Architecture

```
┌──────────────────────────────────────────────────────┐
│  Container                                           │
│                                                      │
│  ┌──────────────────┐     ┌─────────────────────┐    │
│  │ repl_server.py   │────▸│ lake exe repl       │    │
│  │ (HTTP server)    │◂────│ (persistent process) │    │
│  │ port 8000        │     │ stdin/stdout JSON    │    │
│  └──────────────────┘     └─────────────────────┘    │
│         │                         │                  │
│         │                         ▼                  │
│         │              /project/mathlib_env.olean     │
│         │              (pre-pickled Mathlib env)      │
│         │                                            │
└─────────┼────────────────────────────────────────────┘
          │
     HTTP requests
```

### Startup sequence

1. Container starts `repl_server.py`
2. Server spawns `lake env repl` as a subprocess (stdin/stdout pipes)
3. Server sends `{"unpickleEnvFrom": "/project/mathlib_env.olean"}`
   to load the pre-pickled Mathlib environment
4. REPL responds with `{"env": 0}` — this is the base Mathlib env
5. Server is now ready to accept HTTP requests

### Request handling

1. HTTP POST arrives with Lean code (e.g. `#check Real.sqrt`)
2. Server sends `{"cmd": "<code>", "env": 0}` to the REPL process
   (always using env 0 = the base Mathlib environment)
3. REPL evaluates and returns JSON with messages, sorries, new env number
4. Server translates REPL response to the existing API format:
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

- **No olean loading per request** — the REPL process loads Mathlib once
  (at startup via unpickle) and keeps it in memory
- **Pickling uses mmap** — unpickling the pre-built `.olean` is much faster
  than `import Mathlib` (which parses and processes each module)
- **Persistent process** — no subprocess spawn overhead per request

## Build steps

### 1. Dockerfile.mathlib4-repl

Based on `ghcr.io/ldct/mathlib4:v4.27.0`.

```dockerfile
FROM ghcr.io/ldct/mathlib4:v4.27.0

# Install python3 and git (for lake)
RUN apt-get update && apt-get install -y python3 git && rm -rf /var/lib/apt/lists/*

# Clone and build lean-repl (matching Lean version)
RUN cd /opt && \
    git clone --branch v4.27.0 --depth 1 \
      https://github.com/leanprover-community/repl.git && \
    cd repl && lake build repl

# Pre-pickle the Mathlib environment at build time
# This runs `import Mathlib` once and saves the environment
RUN cd /project && \
    echo '{"cmd": "import Mathlib", "env": 0}' | \
      lake env /opt/repl/.lake/build/bin/repl > /tmp/repl_init.json && \
    echo '{"pickleTo": "/project/mathlib_env.olean", "env": 0}' | \
      lake env /opt/repl/.lake/build/bin/repl
    # Note: need to verify exact pickling workflow — may need
    # both commands in one session separated by blank line

COPY repl_server.py /repl_server.py

EXPOSE 8000
CMD ["python3", "/repl_server.py"]
```

**Open question**: The pickle step needs both the import and pickleTo in the
same REPL session. The input should be:
```
{"cmd": "import Mathlib"}

{"pickleTo": "/project/mathlib_env.olean", "env": 0}
```
(Commands separated by blank lines.)

### 2. repl_server.py

Python HTTP server that:
- Spawns `lake env /opt/repl/.lake/build/bin/repl` on startup
- Unpickles `/project/mathlib_env.olean` to get base env
- Handles POST requests by sending `{"cmd": ..., "env": 0}` to REPL
- Reads JSON response line from REPL stdout
- Translates to API response format
- Handles REPL process crashes with automatic restart
- Serializes requests (single REPL process, one at a time)

Key implementation details:
- Use `subprocess.Popen` with `stdin=PIPE, stdout=PIPE`
- Read responses by looking for complete JSON objects (one per line)
- Commands separated by blank lines (write `json + "\n\n"`)
- Thread lock to serialize access to the REPL process
- Watchdog to restart REPL if it crashes

### 3. Cloudflare deployment

- Push new image as `mathlib4-repl-server:v4.27.0`
- Add new container class `Mathlib4v27ReplContainer` in wrangler.jsonc
- Add new route `mathlib-repl-4-27-0` in Worker
- Keep existing `mathlib-4-27-0` endpoint as fallback
- Instance type: `standard-3` (16GB disk for 10GB image)

## Expected performance

| Scenario                     | Current  | With REPL  |
|------------------------------|----------|------------|
| Container cold start         | ~2s      | ~2s + unpickle time |
| First request (unpickle)     | N/A      | ~5-15s (one-time) |
| Subsequent requests          | 3-75s    | <1s (no import needed) |
| `#check Real.sqrt`           | ~75s     | <1s |
| `#eval Nat.factorial 10`     | ~3s      | <1s |
| Prove a Mathlib theorem      | ~20s     | ~1-5s (just tactic execution) |

The massive improvement is that **Mathlib is already loaded** in the REPL
process. Each request only needs to type-check/evaluate the user's code,
not re-import thousands of modules.

## Risks & mitigations

1. **Pickle file too large** — Mathlib env pickle could be several GB.
   Mitigation: pickling only stores *changes* relative to imports, so it
   should be small. If too large, skip pickling and just do
   `{"cmd": "import Mathlib"}` at startup (slower startup, same steady-state).

2. **REPL process memory leak** — long-lived process may accumulate state.
   Mitigation: restart REPL after N requests or if memory exceeds threshold.

3. **REPL crash on bad input** — malicious code could crash the REPL.
   Mitigation: catch crashes, auto-restart, return error to user.

4. **Concurrency** — single REPL process is single-threaded.
   Mitigation: serialize requests with a lock. Cloudflare can run
   multiple container instances for parallelism.

5. **lean-repl v4.27.0 compat** — need to verify the repl builds with
   the mathlib project's toolchain.
   Mitigation: there's a tagged release `v4.27.0` of lean-repl.

## Files to create

1. `lean4-dockerfiles/Dockerfile.mathlib4-repl` — Docker build
2. `lean4-dockerfiles/repl_server.py` — HTTP ↔ REPL bridge
3. `lean4-server-cf/wrangler.jsonc` — add container + route
4. `lean4-server-cf/src/index.ts` — add route handling

## Testing plan

1. Build Docker image locally
2. Test REPL process manually: `docker run --rm -it <image> lake env /opt/repl/.lake/build/bin/repl`
3. Test pickling: verify pickle/unpickle cycle
4. Test HTTP server: health check, simple eval, Mathlib theorem
5. Measure cold start and per-request latency
6. Push to Cloudflare and test end-to-end
