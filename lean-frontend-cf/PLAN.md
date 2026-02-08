# Lean 4 Web Editor — Plan

## Goal
Self-contained single-page web editor (CodeMirror 6) that POSTs Lean code to
`https://lean4-servers.xuanji.workers.dev/{version}` and displays the result.

UI modeled on https://live.lean-lang.org/:
- **Top bar**: version toggle, Run button, status indicator
- **Left panel**: CodeMirror 6 editor with Lean-ish syntax highlighting
- **Right panel**: output pane showing stdout, stderr, errors, and metadata
- **Resizable split** between panels (vertical divider)

## Key Differences from live.lean-lang.org
| live.lean-lang.org | This project |
|-|-|
| LSP (incremental, per-cursor) | Batch POST (whole file, explicit Run) |
| Real-time diagnostics inline | Output in right panel after execution |
| Mathlib available | Bare Lean only (no imports beyond prelude) |

## Architecture

```
lean-frontend-cf/
├── index.html          # single entry point
├── style.css           # layout & theme
├── app.js              # editor setup, API calls, UI logic
└── PLAN.md             # this file
```

All dependencies (CodeMirror) loaded from CDN — no build step.

## UI Layout

```
┌──────────────────────────────────────────────────────────┐
│  [Lean 4 Editor]   [v4.24 ▾ v4.25 v4.26 v4.27 v4.28]  │
│                                          [▶ Run] [⏳]   │
├─────────────────────────┬────────────────────────────────┤
│                         │  Output                        │
│   CodeMirror Editor     │  ┌──────────────────────────┐  │
│                         │  │ stdout: 2                │  │
│   #eval 1 + 1           │  │ stderr:                  │  │
│   #check Nat.add_comm   │  │ exit: 0  elapsed: 0.5s   │  │
│                         │  └──────────────────────────┘  │
│                         │                                │
│                         │  Errors / Warnings (if any)    │
│                         │  rendered with line numbers    │
├─────────────────────────┴────────────────────────────────┤
│  status bar: version · elapsed · connection state        │
└──────────────────────────────────────────────────────────┘
```

## Version Toggle
- Segmented button group (pill-style) in the top bar
- Available versions: `lean-4-24-0`, `lean-4-25-0`, `lean-4-26-0`, `lean-4-27-0`, `lean-4-28-0-rc1`
- Selection persisted in `localStorage`
- Switching version does NOT auto-run; user re-runs manually

## Run Behavior
- **Trigger**: click ▶ Run button **or** Ctrl/Cmd+Enter
- POST body is raw editor text (`Content-Type: text/plain`)
- While running: button shows spinner, editor is not disabled
- On response: right panel updates with formatted stdout/stderr/exit/elapsed
- On error (network, timeout): right panel shows error message in red
- Debounce: ignore rapid duplicate clicks

## Right Panel Output Format
- **Stdout** section: monospace, preserves whitespace, green left-border for success
- **Stderr** section: monospace, red left-border if non-empty
- **Metadata line**: exit code, elapsed time, Lean version used
- If stderr contains Lean error messages with line:col, parse and display them
  with clickable line references that jump the cursor in the editor

## CodeMirror Setup
- CodeMirror 6 via CDN (esm.sh or jsdelivr)
- Extensions: line numbers, bracket matching, active line highlight,
  basic syntax highlighting (Lean keywords via StreamLanguage or custom),
  Ctrl+Enter keybinding
- Dark/light theme: follow system `prefers-color-scheme`

## Implementation Steps
1. [x] Create PLAN.md
2. [ ] Scaffold `index.html` with CDN imports, basic layout
3. [ ] Implement `style.css` — split-panel layout, top bar, output styling
4. [ ] Implement `app.js` — CodeMirror init, version toggle, run logic, output rendering
5. [ ] Add Lean keyword highlighting
6. [ ] Add error line parsing + click-to-jump
7. [ ] Test end-to-end with live API
8. [ ] Polish: loading states, keyboard shortcut hints, responsive
9. [ ] Serve via busybox httpd on port 8000

## Serving
```bash
busybox httpd -f -p 8000 -h /home/exedev/lean-frontend-cf
```
Accessible at: https://lean-frontend-cf.exe.xyz:8000/
