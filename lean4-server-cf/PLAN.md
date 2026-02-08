# Lean 4 Server on Cloudflare Containers

## Overview

Deploy the Lean 4 HTTP server (`ghcr.io/ldct/lean4-server:v4.24.0`) to Cloudflare Containers so it's accessible as a public endpoint.

The server accepts POST requests with Lean code and returns evaluation results as JSON.

## How Cloudflare Containers Work

Cloudflare Containers are **not** standalone Docker hosts. They require three components:

1. **A Worker** (TypeScript) — receives HTTP requests from the internet, forwards them to the container
2. **A Docker image** — your application, built and pushed by `wrangler deploy`
3. **A `wrangler.jsonc` config** — ties the Worker to the container, sets instance type and scaling

Containers are backed by Durable Objects. Each container instance is globally routable and spins up on demand. They sleep after inactivity and scale to zero when idle.

## Image Constraints

| Property | Value | Requirement |
|---|---|---|
| Architecture | `linux/amd64` | ✅ Already correct |
| Compressed size | ~672 MB | Must fit in instance disk |
| Uncompressed size | ~2.5 GB | Need ≥4 GB disk |
| Port | 8000 | Set `defaultPort = 8000` in Worker |
| Memory usage | ~256 MB per Lean invocation | Need ≥1 GiB memory |

## Instance Type Selection

Cloudflare offers these instance types:

| Instance Type | vCPU | Memory | Disk |
|---|---|---|---|
| lite | 1/16 | 256 MiB | 2 GB |
| basic | 1/4 | 1 GiB | 4 GB |
| **standard-1** | **1/2** | **4 GiB** | **8 GB** |
| standard-2 | 1 | 6 GiB | 12 GB |
| standard-3 | 2 | 8 GiB | 16 GB |
| standard-4 | 4 | 12 GiB | 20 GB |

**Recommendation: `standard-1`** — 4 GiB memory handles concurrent Lean invocations, 8 GB disk fits the 2.5 GB image comfortably.

`basic` (4 GB disk) is tight with 2.5 GB uncompressed image + runtime overhead. Not recommended.

## Pricing

Requires the **Workers Paid plan** ($5/month). Then pay-per-use:

- **Memory**: 25 GiB-hours/month included, then $0.0000025/GiB-second
- **CPU**: 375 vCPU-minutes/month included, then $0.000020/vCPU-second
- **Disk**: 200 GB-hours/month included, then $0.00000007/GB-second

Charges start when a request hits the container. Charges stop when the container sleeps. With `sleepAfter = "2m"`, a container serving occasional requests will cost very little.

## Cold Start

Cold starts are typically 2-3 seconds for small images. With a 2.5 GB image, expect **5-10 seconds** on first request. Subsequent requests to a running container are fast (the Python server stays up).

## Project Structure

```
lean4-server-cf/
├── PLAN.md              # This file
├── Dockerfile           # Copy of lean4-dockerfiles/Dockerfile.lean4-server
├── lean_server.py       # Copy of lean4-dockerfiles/lean_server.py
├── src/
│   └── index.ts         # Worker: forwards requests to container
├── worker-configuration.d.ts  # TypeScript types for Worker env
├── wrangler.jsonc       # Wrangler config (container, instance type, etc.)
├── package.json
└── tsconfig.json
```

## Worker Design

The Worker is minimal — it just proxies requests to the container:

- `POST /` → forward to container port 8000
- `GET /health` → forward to container port 8000
- All other routes → 404

The container runs as a singleton (one instance). If you need horizontal scaling later, use `getRandom(env.MY_CONTAINER, N)` with N instances.

The Worker sets `sleepAfter = "2m"` so the container stays warm for 2 minutes after the last request.

## wrangler.jsonc Config

```jsonc
{
  "name": "lean4-server",
  "main": "src/index.ts",
  "compatibility_date": "2025-10-08",
  "compatibility_flags": ["nodejs_compat"],
  "containers": [
    {
      "class_name": "LeanContainer",
      "image": "./Dockerfile",
      "instance_type": "standard-1",
      "max_instances": 5
    }
  ],
  "durable_objects": {
    "bindings": [
      {
        "class_name": "LeanContainer",
        "name": "LEAN_CONTAINER"
      }
    ]
  },
  "migrations": [
    {
      "new_sqlite_classes": ["LeanContainer"],
      "tag": "v1"
    }
  ]
}
```

## Prerequisites

1. **Cloudflare account** on the **Workers Paid plan** ($5/month)
2. **`wrangler` CLI** installed: `npm i -g wrangler`
3. **Docker** running locally (wrangler uses it to build and push the image)
4. **Authenticate**: `wrangler login`

## Deployment Steps

```bash
cd lean4-server-cf
npm install
npx wrangler deploy
```

`wrangler deploy` will:
1. Build the Docker image locally using Docker
2. Push the image to Cloudflare's container registry
3. Deploy the Worker with the container binding
4. Wait ~2-3 minutes for container provisioning

After deployment, check status:

```bash
npx wrangler containers list
npx wrangler containers images list
```

The endpoint will be available at `https://lean4-server.<your-subdomain>.workers.dev`.

## Usage

```bash
# Health check
curl https://lean4-server.<subdomain>.workers.dev/health

# Evaluate Lean code
curl -X POST https://lean4-server.<subdomain>.workers.dev/ \
  -d '#eval 1 + 1'
# {"ok": true, "stdout": "2\n", "stderr": "", "exitCode": 0, "elapsed": 0.368}

# With custom timeout
curl -X POST https://lean4-server.<subdomain>.workers.dev/ \
  -H "X-Lean-Timeout: 10" \
  -d '#check Nat.add_comm'
```

## Step 0: Test Workers Setup Without Containers

Before deploying the full container stack, verify the Workers toolchain end-to-end with a **stub Worker** that has no container dependency. This catches account/plan/auth/wrangler issues cheaply.

### What to build

Create a minimal `wrangler.jsonc` and `src/index.ts` with **no** `containers`, `durable_objects`, or `migrations` fields. The Worker should:

- `POST /` → return a hard-coded JSON response mimicking the real server:
  ```json
  {"ok": true, "stdout": "2\n", "stderr": "", "exitCode": 0, "elapsed": 0.0, "stub": true}
  ```
- `GET /health` → return `{"status": "ok", "stub": true}`
- Everything else → 404

Stub `wrangler.jsonc`:

```jsonc
{
  "name": "lean4-server",
  "main": "src/index.ts",
  "compatibility_date": "2025-10-08"
}
```

### Deploy & verify

```bash
cd lean4-server-cf
npm install
npx wrangler deploy          # deploys stub Worker only, no Docker needed
curl https://lean4-server.<subdomain>.workers.dev/health
curl -X POST https://lean4-server.<subdomain>.workers.dev/ -d '#eval 1 + 1'
```

### What this validates

| Concern | Verified? |
|---|---|
| Cloudflare account & Workers Paid plan active | ✅ |
| `wrangler login` credentials work | ✅ |
| Worker deploys and is reachable at expected URL | ✅ |
| Route handling (POST /, GET /health, 404 fallback) | ✅ |
| CORS headers (if added) work from browser | ✅ |
| Custom domain routing (if configured) | ✅ |

### Transition to containers

Once the stub is confirmed working, add the `containers`, `durable_objects`, and `migrations` sections back to `wrangler.jsonc`, replace the stub handler with the real proxy logic, and run `wrangler deploy` again. The URL stays the same — the container deployment is an in-place upgrade.

## TODO

- [ ] Set up Cloudflare account + Workers Paid plan
- [ ] `wrangler login`
- [ ] Scaffold the Worker, config, and package.json
- [ ] **Deploy stub Worker (no containers) and verify routing** ← Step 0
- [ ] Add container config to `wrangler.jsonc` and real proxy to `index.ts`
- [ ] `wrangler deploy` with containers and test
- [ ] Optionally add a custom domain
- [ ] Optionally add authentication (API key header check in Worker)
