# Mathlib REPL Server via Docker

An HTTP server that keeps a [lean-repl](https://github.com/leanprover-community/repl)
process alive with **Mathlib imported once at startup**. Each request then only
type-checks/evaluates your code against the preloaded environment, so requests
return in well under a second instead of re-importing Mathlib (~20–75s) every time.

For the design rationale and performance numbers, see `PLAN-mathlib-repl.md`.
For the simpler one-shot `lake env lean` approach (no persistent process), see
`mathlib4-docker.md`.

## Build

The REPL image is built on top of `ghcr.io/ldct/mathlib4:v4.27.0`:

```bash
docker build -f Dockerfile.mathlib4-repl -t mathlib4-repl:v4.27.0 .
```

## Run

```bash
docker run --rm -p 8000:8000 mathlib4-repl:v4.27.0
```

On startup the server begins importing Mathlib **in the background**, so the HTTP
port is available immediately but requests return `503` until the import finishes.
Poll `/health` and wait for `"ready": true` (the import takes ~20–75s depending on
disk cache).

### Configuration (environment variables)

| Variable | Default | Purpose |
|----------|---------|---------|
| `LEAN_SERVER_HOST` | `0.0.0.0` | Bind address |
| `LEAN_SERVER_PORT` | `8000` | Listen port |
| `LEAN_TIMEOUT` | `120` | Per-command timeout (seconds) |
| `LEAN_SERVER_QUIET` | unset | Suppress per-request access logging when set |

## API

### `GET /health`

Returns readiness. Use this to wait for Mathlib to finish importing.

```bash
curl -s localhost:8000/health
```

```json
{"ready": true, "alive": true, "mathlib": true, "repl": true, "base_env": 0, "status": "ready"}
```

While importing, `status` is `"importing Mathlib"` and `ready` is `false`. On a
startup failure, `status` is `"error: <message>"`.

### `POST /`

The request body is **raw Lean code** (not JSON-wrapped). The server runs it
against the base environment that already has `import Mathlib` loaded.

```bash
curl -s localhost:8000/ --data-binary '#check @Real.sqrt'
```

```json
{
  "ok": true,
  "messages": [
    {"severity": "info", "pos": {"line": 1, "column": 0},
     "endPos": {"line": 1, "column": 6}, "data": "Real.sqrt : ℝ → ℝ"}
  ],
  "sorries": [],
  "env": 1,
  "elapsed": 0.012
}
```

Use `--data-binary` (not `-d`), which would strip newlines — important for
multi-line Lean snippets.

#### Response fields

| Field | Meaning |
|-------|---------|
| `ok` | `false` if any message has `severity == "error"`, else `true` |
| `messages` | REPL diagnostics: `severity` (`info`/`warning`/`error`), `pos`, `endPos`, `data` |
| `sorries` | Unproved goals introduced by `sorry`, each with its position and goal state |
| `env` | The new environment number the REPL created for this command |
| `elapsed` | Server-measured evaluation time in seconds |

#### HTTP status codes

| Status | Condition |
|--------|-----------|
| `200` | Evaluated, no Lean errors (`ok: true`) |
| `400` | Evaluated, but Lean reported an error (`ok: false`) |
| `503` | Server not ready (still importing Mathlib, or import failed) |
| `502` | REPL process crashed; server auto-restarts and re-imports in the background |

> Each request runs against the base Mathlib environment (`base_env`); commands do
> not share state with each other. The returned `env` numbers are informational —
> the server always resets to the base env for the next request.

## Examples

Prove a theorem:

```bash
curl -s localhost:8000/ --data-binary \
  'example : 2 + 2 = 4 := by norm_num'
```

Detect a `sorry`:

```bash
curl -s localhost:8000/ --data-binary \
  'theorem foo : 1 = 1 := by sorry'
# -> ok: true, but "sorries" is non-empty
```

Trigger an error (returns HTTP 400, `ok: false`):

```bash
curl -s localhost:8000/ --data-binary '#check doesNotExist'
```
