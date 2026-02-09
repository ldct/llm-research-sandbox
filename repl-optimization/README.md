# Mathlib REPL Optimization

Investigating and reducing the ~78s Mathlib olean load time in the lean-repl.

## Baseline Measurements (2025-02-09)

### Setup

- **Image**: `mathlib4-repl:v4.27.0` (10.4 GB)
- **Base image**: `ghcr.io/ldct/mathlib4:v4.27.0` (10.1 GB)
- **REPL**: `leanprover-community/repl` v4.27.0
- **Server**: `repl_server.py` — spawns `lake env repl`, sends `{"cmd": "import Mathlib"}` at startup
- **Dockerfile**: `lean4-dockerfiles/Dockerfile.mathlib4-repl`

### Olean load time

| Environment        | Import time | Notes                          |
|--------------------|-------------|--------------------------------|
| Local (exe.dev VM) | **78.3s**   | `docker run`, SSD-backed       |
| Cloudflare Container | **~78s**  | Measured via health poll (60s sleep timeout) |

Times are nearly identical — the bottleneck is CPU-bound olean deserialization, not I/O.

### Request latency (warm)

Once Mathlib is imported, individual requests are fast:

```
POST / with:
  #check Real.sqrt
  example : (2 : ℚ) + 2 = 4 := by norm_num
  #eval (10 : Nat).factorial

Response: 0.44s
```

### Cold start timeline

```
t=0s    Container starts, HTTP server listening
        Health: {ready: false, status: "importing Mathlib"}
t=78s   import Mathlib completes
        Health: {ready: true, status: "ready"}
        Requests now served in <1s
t=138s  No requests for 60s → Cloudflare sleeps container (sleepAfter=60s)
        Next request triggers full cold start again
```

### Architecture

```
repl_server.py
  ├── Spawns: lake env /opt/repl/.lake/build/bin/repl
  ├── Sends: {"cmd": "import Mathlib"} → waits 78s → gets env=0
  ├── Per request: {"cmd": <user code>, "env": 0} → response in <1s
  └── Singleton on Cloudflare (all users share one container)
```

The REPL is a single long-lived process. Each request reuses the base Mathlib environment (env=0) so import cost is paid only once.

## Ideas to Explore

- **Selective imports**: Import only commonly-used Mathlib modules instead of all of Mathlib
- **LEAN_IMPORT_PARALLEL**: Environment variable to control parallel olean loading threads
- **Prewarmed snapshots**: Serialize the post-import REPL state to disk, reload on startup
- **Keep-alive pings**: Prevent Cloudflare sleep by pinging every 50s from a cron/worker
- **Increase sleepAfter**: Raise from 60s to 300s to reduce cold starts
- **Profile the import**: Identify which Mathlib modules take longest to deserialize
