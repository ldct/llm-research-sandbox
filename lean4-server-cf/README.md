# Lean 4 Servers on Cloudflare Containers

Multi-version Lean 4 evaluation API running on Cloudflare Workers + Containers.

**Base URL**: `https://lean4-servers.xuanji.workers.dev`

## Endpoints

### Plain Lean (no Mathlib)

`lean-4-24-0` · `lean-4-25-0` · `lean-4-26-0` · `lean-4-27-0` · `lean-4-28-0-rc1`

| Method | Path | Description |
|--------|------|-------------|
| `POST` | `/{version}` | Evaluate Lean code (warm singleton container) |
| `POST` | `/{version}/cold` | Evaluate Lean code (forces fresh container cold start) |
| `GET`  | `/{version}/health` | Health check — returns Lean version string |

Containers sleep after 10s of inactivity. Warm requests take ~0.4-0.9s.
Cold starts take ~3-5s.

### Mathlib — batch mode

`mathlib-4-27-0`

Same endpoint pattern as plain Lean. Each request spawns `lake env lean <file>` in a
project with Mathlib dependencies pre-built. Code is written to `/project/MathProject.lean`
before each run.

Containers sleep after 120s. Targeted imports (e.g. `import Mathlib.Data.Nat.Factorial.Basic`)
take ~3s warm / ~23s cold. Full `import Mathlib` takes ~75s (disk I/O bound — loads ~5.2GB
of build artifacts).

### Mathlib — REPL mode (recommended)

`mathlib-repl-4-27-0`

A persistent [lean-repl](https://github.com/leanprover-community/repl) process that imports
Mathlib **once** at container startup (~75s), then handles all subsequent requests in
sub-second time. This is the recommended endpoint for Mathlib usage.

Containers sleep after 60s.

| Method | Path | Description |
|--------|------|-------------|
| `POST` | `/mathlib-repl-4-27-0` | Evaluate Lean code (Mathlib pre-loaded) |
| `POST` | `/mathlib-repl-4-27-0/cold` | Force fresh container |
| `GET`  | `/mathlib-repl-4-27-0/health` | Health check — includes `ready` field |

**Important**: Do **not** include `import Mathlib` in your code — Mathlib is already loaded
in the REPL environment. Just use Mathlib definitions and tactics directly.

## Response Formats

### Plain Lean & Mathlib batch

```json
{"ok": true, "stdout": "2\n", "stderr": "", "exitCode": 0, "elapsed": 0.5}
```

### Mathlib REPL

Returns structured messages with line/column positions:

```json
{
  "ok": true,
  "messages": [
    {
      "severity": "info",
      "pos": {"line": 1, "column": 0},
      "endPos": {"line": 1, "column": 6},
      "data": "Real.sqrt (x : ℝ) : ℝ"
    }
  ],
  "env": 1,
  "elapsed": 0.019
}
```

Messages have `severity` of `"info"`, `"warning"`, or `"error"`. The `env` field is the
REPL environment number (can be ignored — each request gets a fresh env based on the
Mathlib base env).

### REPL health check

```json
{"ready": true, "alive": true, "mathlib": true, "repl": true, "base_env": 0, "status": "ready"}
```

When `ready` is `false`, Mathlib is still importing — requests will be queued.

## Examples

### Plain Lean

```bash
# Evaluate an expression
curl -X POST https://lean4-servers.xuanji.workers.dev/lean-4-27-0 \
  -d '#eval 1 + 1'
# {"ok": true, "stdout": "2\n", "stderr": "", "exitCode": 0, "elapsed": 0.5}

# Check a type
curl -X POST https://lean4-servers.xuanji.workers.dev/lean-4-27-0 \
  -d '#check Nat.add_comm'

# Prove a theorem
curl -X POST https://lean4-servers.xuanji.workers.dev/lean-4-28-0-rc1 \
  -d 'theorem t : ∀ (a b : Nat), a + b = b + a := by omega'

# Cold start (new container each time, for benchmarking)
curl -X POST https://lean4-servers.xuanji.workers.dev/lean-4-27-0/cold \
  -d '#eval 1 + 1'

# Health check
curl https://lean4-servers.xuanji.workers.dev/lean-4-27-0/health
```

### Mathlib (REPL — recommended)

```bash
# Check a Mathlib definition (sub-second!)
curl -X POST https://lean4-servers.xuanji.workers.dev/mathlib-repl-4-27-0 \
  -d '#check Real.sqrt'

# Prove with Mathlib tactics
curl -X POST https://lean4-servers.xuanji.workers.dev/mathlib-repl-4-27-0 \
  -d 'example : (2 : ℚ) + 2 = 4 := by norm_num'

# Use sorry — returns proof state goals
curl -X POST https://lean4-servers.xuanji.workers.dev/mathlib-repl-4-27-0 \
  -d 'theorem foo : 1 = 2 := by sorry'

# Health check (check "ready" field before sending requests)
curl https://lean4-servers.xuanji.workers.dev/mathlib-repl-4-27-0/health
```

### Mathlib (batch — slower)

```bash
# Targeted import (~3s warm, ~23s cold)
curl -X POST https://lean4-servers.xuanji.workers.dev/mathlib-4-27-0 \
  -d 'import Mathlib.Data.Nat.Factorial.Basic
#eval (10 : Nat).factorial'

# Full Mathlib import (~75s — use REPL mode instead)
curl -X POST https://lean4-servers.xuanji.workers.dev/mathlib-4-27-0 \
  -H "X-Lean-Timeout: 120" \
  -d 'import Mathlib
#check Real.sqrt'
```

## Performance

### Plain Lean

| Scenario | Time |
|----------|------|
| Warm request | 0.4–0.9s |
| Cold start | 3–5s |

### Mathlib REPL (recommended)

| Scenario | Time |
|----------|------|
| Container startup (import Mathlib) | ~75s (one-time) |
| `#check` / `#eval` (warm) | **20–50ms** |
| Tactic proofs (warm) | **40–350ms** |

### Mathlib batch

| Scenario | Time |
|----------|------|
| Targeted import (warm) | ~3s |
| Targeted import (cold) | ~23s |
| Full `import Mathlib` | ~75s |

## Architecture

A single Cloudflare Worker (`src/index.ts`) routes requests to Durable Objects backed
by containers. Routing is by `METHOD /path` pattern match.

```
client → Worker (routes by path) → Durable Object → Container
```

### Three server types

| Server | Image | Process | Use case |
|--------|-------|---------|----------|
| `lean_server.py` | `lean4-server:*` | `lean --stdin` per request | Plain Lean |
| `mathlib_server.py` | `mathlib4-server:*` | `lake env lean <file>` per request | Mathlib (batch) |
| `repl_server.py` | `mathlib4-repl:*` | Persistent `lean-repl` process | Mathlib (fast) |

### Container config

| Endpoint pattern | Instance type | Sleep timeout | Disk |
|-----------------|---------------|---------------|------|
| `lean-4-*` | standard-1 (½ vCPU, 4GB RAM, 8GB disk) | 10s | 8GB |
| `mathlib-4-*` | standard-3 (½ vCPU, 4GB RAM, 16GB disk) | 120s | 16GB |
| `mathlib-repl-4-*` | standard-3 (½ vCPU, 4GB RAM, 16GB disk) | 60s | 16GB |

Mathlib images unpack to ~10.1GB, requiring standard-3 (16GB disk). The standard-1
default (8GB) fails with `ImagePullError`.

### Singleton vs cold

The `/cold` endpoint uses `ns.newUniqueId()` to force a fresh Durable Object + container
on every request, bypassing the warm singleton. Useful for benchmarking cold start times.

All other endpoints use `ns.idFromName("singleton")` — a single persistent container
per version that stays alive until the sleep timeout expires.

### CORS

All responses include `Access-Control-Allow-Origin: *` headers. The Worker handles
`OPTIONS` preflight requests.

## Docker Images

| Image | Base | Size (compressed) | Registry |
|-------|------|--------------------|----------|
| `lean4-server:v4.X.Y` | `ghcr.io/ldct/lean4:v4.X.Y` | ~250MB | Cloudflare + GHCR |
| `mathlib4-server:v4.27.0` | `ghcr.io/ldct/mathlib4:v4.27.0` | ~3.3GB | Cloudflare |
| `mathlib4-repl:v4.27.0` | `ghcr.io/ldct/mathlib4:v4.27.0` | ~3.3GB | Cloudflare |

Dockerfiles are in `../lean4-dockerfiles/`.

## Deploying

```bash
# Push a container image
npx wrangler containers push <local-image:tag>

# Deploy the Worker
npx wrangler deploy

# Check container status
npx wrangler containers list
npx wrangler containers info <ID>
```

Authentication is via `CLOUDFLARE_API_KEY` and `CLOUDFLARE_EMAIL` in `.env`.
