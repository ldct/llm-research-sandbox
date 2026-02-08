# Lean 4 Servers on Cloudflare Containers

Multi-version Lean 4 evaluation API running on Cloudflare Workers + Containers.

**Base URL**: `https://lean4-servers.xuanji.workers.dev`

## Versions

`lean-4-24-0` · `lean-4-25-0` · `lean-4-26-0` · `lean-4-27-0` · `lean-4-28-0-rc1`

## Endpoints

| Method | Path | Description |
|--------|------|-------------|
| `POST` | `/{version}` | Evaluate Lean code (warm singleton container) |
| `POST` | `/{version}/cold` | Evaluate Lean code (forces fresh container cold start) |
| `GET`  | `/{version}/health` | Health check — returns Lean version string |

Containers sleep after 10s of inactivity. First request after sleep incurs ~3-5s Lean startup. Warm requests take ~0.4-0.9s.

## Examples

```bash
# Evaluate an expression
curl -X POST https://lean4-servers.xuanji.workers.dev/lean-4-27-0 \
  -d '#eval 1 + 1'
# {"ok": true, "stdout": "2\n", "stderr": "", "exitCode": 0, "elapsed": 0.5}

# Check a type
curl -X POST https://lean4-servers.xuanji.workers.dev/lean-4-27-0 \
  -d '#check Nat.add_comm'
# {"ok": true, "stdout": "Nat.add_comm (n m : Nat) : n + m = m + n\n", ...}

# Prove a theorem
curl -X POST https://lean4-servers.xuanji.workers.dev/lean-4-28-0-rc1 \
  -d 'theorem t : ∀ (a b : Nat), a + b = b + a := by omega'

# Cold start (new container each time, for benchmarking)
curl -X POST https://lean4-servers.xuanji.workers.dev/lean-4-27-0/cold \
  -d '#eval 1 + 1'

# Health check
curl https://lean4-servers.xuanji.workers.dev/lean-4-27-0/health
# {"version": "Lean (version 4.27.0, ...)"}
```

## Architecture

A single Cloudflare Worker routes requests by version to Durable Objects backed by containers running `ghcr.io/ldct/lean4-server`. Each container runs a Python HTTP server that pipes input to `lean --stdin`.

The `/cold` endpoint uses `ns.newUniqueId()` to force a fresh Durable Object + container on every request, bypassing the warm singleton.
