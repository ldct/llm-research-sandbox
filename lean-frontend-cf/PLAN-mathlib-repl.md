# Frontend: Mathlib REPL Support — Plan

## Goal

Add `mathlib-repl-4-27-0` as a version option in the editor. Handle the different
response format and the ~75s cold start gracefully in the UI.

## Changes

### 1. Version toggle

Add a visually separated "Mathlib" group to the version toggle bar:

```
[4.24] [4.25] [4.26] [4.27] [4.28-rc1]  |  [Mathlib 4.27]
```

Use a CSS divider/separator between plain Lean and Mathlib versions.
The VERSIONS array gets a new entry with a `repl: true` flag.

### 2. Health polling & startup banner

When a Mathlib version is selected (or on page load if already selected):
- Immediately `GET /mathlib-repl-4-27-0/health`
- If `ready: false`, show a **banner** across the top of the output pane:
  - "⏳ Loading Mathlib… (this takes ~60s on first request)"
  - Include a progress-style animation (pulsing bar or spinner)
  - Poll `/health` every 5s until `ready: true`
  - When ready, replace banner with "✓ Mathlib loaded" (fade out after 3s)
- If `ready: true`, show nothing (or brief "✓ Mathlib ready")
- If health returns an error (503 = container provisioning), show:
  - "⏳ Starting Mathlib container… (this takes ~2-3 min on cold start)"

The banner sits inside `#output-content`, above any output.

### 3. Run behavior with REPL

When running against a REPL endpoint:
- If health shows `ready: false`, still allow clicking Run but show
  "Waiting for Mathlib to load…" in the output pane (the server queues
  the request internally, so it will eventually return)
- On success, render using the **messages format** instead of stdout/stderr

### 4. Output rendering for REPL responses

The REPL returns `{ ok, messages, sorries, env, elapsed }` instead of
`{ ok, stdout, stderr, exitCode, elapsed }`.

New `renderReplOutput(data, wallMs)` function:
- Group messages by severity (info, warning, error)
- Each message rendered as a block with:
  - Clickable `line:col` prefix (jumps to editor line)
  - Color-coded: info=green, warning=amber, error=red
  - The `data` field as the message body
- Sorries section: show goal text for each sorry with position
- Keep the elapsed/wall time footer

Detect which renderer to use based on presence of `messages` key in response.

### 5. Examples

Add a "Mathlib" example that auto-selects the mathlib-repl version:
```lean
-- Mathlib is pre-loaded — no import needed!
#check Real.sqrt
example : (2 : ℚ) + 2 = 4 := by norm_num
#eval (10 : Nat).factorial
```

### 6. Status bar

When mathlib-repl is selected, status bar shows:
- "Mathlib 4.27" instead of "Lean 4.27"
- During health poll: "Loading Mathlib…" in the state area
- After ready: "Ready"

## Files to modify

- `app.js` — VERSIONS array, health polling, REPL output renderer, example
- `style.css` — banner styles, version separator, message severity colors
- `index.html` — version toggle separator markup

## Non-goals

- No per-line inline diagnostics (would need CM lint integration)
- No streaming output
- No switching REPL env between requests (each request is independent)
