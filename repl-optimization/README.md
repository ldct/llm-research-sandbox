# Mathlib REPL Optimization

Investigating and reducing the ~28s Mathlib olean load time in the lean-repl.

## Baseline Measurements (2025-02-09)

### Setup

- **Image**: `mathlib4-repl:v4.27.0` (10.4 GB)
- **Base image**: `ghcr.io/ldct/mathlib4:v4.27.0` (10.1 GB)
- **REPL**: `leanprover-community/repl` v4.27.0
- **Server**: `repl_server.py` — spawns `lake env repl`, sends `{"cmd": "import Mathlib"}` at startup
- **Dockerfile**: `lean4-dockerfiles/Dockerfile.mathlib4-repl`
- **Machine**: 2-core VM, SSD-backed
- **Olean files**: 7,878 files, 5.4 GB (Mathlib alone)

### Import time

| Method              | Time    | Notes                          |
|---------------------|---------|--------------------------------|
| `import Mathlib`    | **28s** | Full command elaboration        |
| Pickle unpickle     | **15s** | Still calls `importModules` internally |

Note: earlier measurements showed ~78s when other load was on the machine. The CPU-bound
olean deserialization is sensitive to available CPU.

### Request latency (warm)

Once Mathlib is imported, individual requests are fast:

```
POST / with:
  #check Real.sqrt
  example : (2 : ℚ) + 2 = 4 := by norm_num
  #eval (10 : Nat).factorial

Response: 0.44s
```

### Cold start timeline (Cloudflare Containers)

```
t=0s    Container starts, HTTP server listening
        Health: {ready: false, status: "importing Mathlib"}
t=28s   import Mathlib completes
        Health: {ready: true, status: "ready"}
        Requests now served in <1s
t=88s   No requests for 60s → Cloudflare sleeps container (sleepAfter=60s)
        Next request triggers full cold start again
```

### Architecture

```
repl_server.py
  ├── Spawns: lake env /opt/repl/.lake/build/bin/repl
  ├── Sends: {"cmd": "import Mathlib"} → waits ~28s → gets env=0
  ├── Per request: {"cmd": <user code>, "env": 0} → response in <1s
  └── Singleton on Cloudflare (all users share one container)
```

The REPL is a single long-lived process. Each request reuses the base Mathlib environment (env=0) so import cost is paid only once.

## Approaches Investigated

### 1. REPL Pickle (tested — partial improvement, broken tactics)

The lean-repl has built-in `pickleTo`/`unpickleEnvFrom` commands that serialize
a `CommandSnapshot` to disk.

**What the pickle actually stores:**
- `env.header.imports` — the import list (e.g. `[Mathlib]`)
- `env.constants.map₂` — only the *delta* (new constants added after import)
- Command state and context

**What unpickle does:**
```lean
let env ← (← importModules imports {} 0 (loadExts := true)).replay (Std.HashMap.ofList map₂.toList)
```
It **still calls `importModules`** — all 7,878 olean files are still loaded from disk.
The speedup (28s → 15s) comes from skipping command elaboration overhead, not from
skipping olean loading.

**Fatal problem:** Tactics that rely on `[init]` extensions crash after unpickle:
```
libc++abi: terminating due to uncaught exception of type lean::exception:
  cannot evaluate `[init]` declaration 'Mathlib.Meta.NormNum.normNumExt' in the same module
```
Affected: `norm_num`, `simp`, `omega`, and most Mathlib tactics. Only `rfl` and
basic kernel-level operations work. **This makes pickle unusable for production.**

**Files:** `generate_pickle.py`, `repl_server_pickle.py`, `Dockerfile.mathlib4-repl-pickle`

### 2. CRIU Process Checkpointing (infeasible)

CRIU (Checkpoint/Restore In Userspace) would snapshot the entire REPL process memory
after import, then restore it on cold start. This would preserve all `[init]` extensions
and tactic state.

**Why it won't work:**
- Requires kernel `CONFIG_CHECKPOINT_RESTORE=y` — not available on our VM or Cloudflare
- Requires `/proc/sys/kernel/ns_last_pid` to restore exact PIDs
- Requires `CAP_SYS_PTRACE` and root privileges
- Cloudflare Containers is a sandboxed environment with no kernel control

### 3. `-j` / `--threads` flag (limited by hardware)

Lean's `--threads` flag controls the task manager thread count. Default is hardware
concurrency (2 on our VM). The olean loading pipeline:

1. `readModuleDataParts` — C++ extern, mmaps olean files from disk
2. `finalizeImport` — builds constant maps, processes extensions (sequential loop)
3. `finalizePersistentExtensions` — runs `[init]` declarations

Steps 2-3 are largely sequential. More threads would only help on machines with >2 cores,
and the benefit is limited since the bottleneck is sequential map building and extension
initialization, not parallel file I/O.

## Remaining Ideas to Explore

### 4. Selective imports

Import only commonly-used Mathlib modules instead of all of Mathlib. This directly
reduces the number of olean files loaded.

**Approach:**
- Profile which Mathlib modules users actually use (from logs)
- Create a curated import list (e.g. `import Mathlib.Tactic`, `import Mathlib.Data.Real.Basic`)
- Measure load time with reduced imports

**Expected impact:** Proportional to the fraction of Mathlib imported. Importing 10%
of Mathlib should give roughly ~3s load time.

**Tradeoff:** Users can't use all of Mathlib — requests using unimported modules will fail.

### 5. Keep-alive pings

Avoid cold starts entirely by pinging the container every 50s from a Cloudflare Worker
or external cron to prevent the 60s sleep timeout.

**Pros:** Zero cold starts, trivial to implement  
**Cons:** Container runs 24/7, costs money, doesn't help if container crashes

### 6. Increase `sleepAfter`

Raise from 60s to 300s+ to reduce frequency of cold starts.

**Pros:** Simple config change  
**Cons:** Still has cold starts, just less frequent

### 7. Profile the import pipeline

Instrument `importModules` to identify which phase dominates:
- File I/O (mmap)
- Constant map construction
- Extension initialization (`finalizePersistentExtensions`)
- `[init]` declaration evaluation

This would tell us where optimization effort should focus.
