# Extracting & Testing Lean Textbooks Against the Mathlib REPL

This document describes the workflow for taking Lean 4 textbook source code,
patching it for the Mathlib REPL endpoint, and producing verified example files.

## Architecture

```
Textbook repo (GitHub)
  └─ solution .lean files (with `import Mathlib.*`)
       │
       ▼  strip imports, apply patches
  Cleaned .lean files (no imports, fixes for API drift)
       │
       ▼  POST to REPL endpoint
  Mathlib REPL (all of Mathlib pre-loaded)
       │
       ▼  JSON response: {ok, messages, sorries, elapsed}
  Pass/fail result
       │
       ▼  concatenate passing files
  Single verified example file (e.g. mil-all.lean)
```

## The REPL Endpoint

The Mathlib REPL is a stateful Lean 4 process with all of Mathlib pre-imported.
It accepts raw Lean code via HTTP POST and returns a JSON response.

```bash
# Health check
curl https://<endpoint>/health
# → {"ready": true, "mathlib": true, "repl": true, ...}

# Run code
curl -X POST https://<endpoint>/ --data-binary 'example : 1 + 1 = 2 := by norm_num'
# → {"ok": true, "messages": [], "sorries": [], "env": 1, "elapsed": 0.01}

# Run from file
curl -X POST https://<endpoint>/ --data-binary @myfile.lean
```

**Key constraints:**
- `import` statements are **forbidden** — the REPL already has everything loaded.
- Files must contain at least one declaration (a bare comment file returns "unexpected end of input").
- The `env` field increments with each request (the REPL is stateful, but each request gets a fresh env checkpoint).
- Large files (>100KB) may time out. Keep individual test files reasonable.
- The REPL runs a **specific Mathlib version** which may differ from what the textbook targets.

## Step-by-Step: Adding a New Textbook

### 1. Clone and Inspect

```bash
git clone --depth 1 https://github.com/org/textbook.git /tmp/textbook
cat /tmp/textbook/lean-toolchain          # which Lean version?
find /tmp/textbook -name '*.lean' | wc -l # how many files?
head -20 /tmp/textbook/SomeFile.lean      # what do they import?
```

**Check for deal-breakers:**
- Custom tactic libraries (e.g. `Library.Tactic.Addarith` in math2001) → probably won't work
- Game framework DSL (`World`, `Level`, `TheoremTab`) → not standard Lean, skip
- Lean 3 syntax (`begin`/`end`, `open_locale`) → skip
- Only `import Mathlib.*` or `import Mathlib.Tactic` → good candidate

### 2. Identify Solution Files

Textbooks typically have:
- **Exercise files** with `sorry` placeholders (for students)
- **Solution files** with completed proofs (what we want)

Common patterns:
```
MIL/C02_Basics/solutions/Solutions_S01.lean     # Mathematics in Lean
Solutions/Section01logic/Sheet1.lean             # Formalising Mathematics
Compfiles/Imo2020P2.lean                         # Competition math
```

Use solution files. Skip exercise-only files (they have `sorry`s by design).

### 3. Strip Imports

The most basic transformation — remove all `import` lines:

```bash
grep -v '^import ' file.lean > cleaned.lean
```

For files with custom macros (like compfiles' `ProblemExtraction`):

```python
import re

def strip_compfiles(content):
    # Remove imports
    lines = [l for l in content.split('\n') if not l.startswith('import ')]
    content = '\n'.join(lines)
    # Remove custom macro blocks
    content = re.sub(r'problem_file\s*\{[^}]*\}', '', content, flags=re.DOTALL)
    # Keep snip content but remove markers
    content = content.replace('snip begin', '').replace('snip end', '')
    # Replace custom decl keywords with standard ones
    content = re.sub(r'^problem\b', 'theorem', content, flags=re.MULTILINE)
    content = re.sub(r'^determine\b', 'noncomputable def', content, flags=re.MULTILINE)
    return content
```

### 4. Test Individually

```bash
for f in solutions/*.lean; do
    code=$(grep -v '^import ' "$f")
    result=$(curl -s --max-time 60 -X POST "$ENDPOINT" --data-binary "$code")
    ok=$(echo "$result" | python3 -c "import sys,json; print(json.load(sys.stdin).get('ok'))")
    echo "$ok $f"
done
```

Expect failures. Categorize them before fixing.

### 5. Identify and Apply Patches

Mathlib evolves rapidly. Common breakage patterns between versions:

#### Lemma Renames
| Old Name | New Name | Affected |
|----------|----------|----------|
| `abs_add` | `abs_add_le` | triangle inequality |
| `inv_mul_self` | `inv_mul_cancel` | group theory |
| `mul_inv_self` | `mul_inv_cancel` | group theory |
| `differentiableAt_id'` | `differentiableAt_id` | calculus |
| `Function.funext_iff` | `funext_iff` | moved out of namespace |
| `triv` | `trivial` | removed alias |

To find the new name, use `#check` or `exact?` on the REPL:
```bash
curl -X POST $ENDPOINT --data-binary '#check @abs_add_le'
```

#### Argument Order Swaps
`add_le_add_left` and `add_le_add_right` **swapped** between Mathlib versions:
- **Old**: `add_le_add_left h a` gives `a + b ≤ a + c`
- **New**: `add_le_add_left h a` gives `b + a ≤ c + a`

Fix: swap `left` ↔ `right`.

#### Type/Structure Renames
| Old | New |
|-----|-----|
| `Basis ι K V` | `Module.Basis ι K V` |
| `HasQuotient.quotient'` | `HasQuotient.Quotient` |

#### Notation/Parsing Changes
Subscript digits in custom notation (e.g. `≤₁`) may be parsed differently
in newer Lean. Fix by adding explicit parentheses:
```lean
-- Breaks: c * a ≤₁ c * b
-- Works:  (c * a) ≤₁ (c * b)
```

#### Tactic Behavior Changes
- `peel` tactic binds variables differently → rewrite proof manually
- `use x, y` may fill too many goals → use `exact ⟨x, y, by omega⟩`
- `field_simp` may leave arithmetic subgoals → add `norm_num` after
- `simp` lemma set changes → some `simp` calls need updated lemma lists

#### Applying Fixes in Batch
```bash
# Simple renames
find . -name '*.lean' -exec sed -i 's/\babs_add\b/abs_add_le/g' {} +
find . -name '*.lean' -exec sed -i 's/\btriv\b/trivial/g' {} +

# For multi-line or complex fixes, use Python:
python3 -c "
with open('file.lean') as f: content = f.read()
content = content.replace('old pattern', 'new pattern')
with open('file.lean', 'w') as f: f.write(content)
"
```

### 6. Handle Cross-File Dependencies

Some textbooks have files that import from earlier files in the same book:
```
Sheet5.lean imports Sheet3.lean  (for TendsTo definition)
Sheet6.lean imports Sheet5.lean
```

Fix by **prepending** the dependency content:
```bash
cat Sheet3_cleaned.lean Sheet5_cleaned.lean > Sheet5_merged.lean
```

### 7. Concatenate into a Single File

This is the trickiest step due to name collisions and scope leakage.

**Problems to handle:**
- `open` statements leak across file boundaries → wrap each file in `section`
- Duplicate top-level names (e.g. `aux`, `FnUb`) → rename with suffix
- Unclosed `namespace`/`section` blocks → auto-close them
- `namespace` wrappers break dot notation → use `section` instead

**The working approach:**

```python
import re

all_names_seen = {}

for i, (filename, content) in enumerate(files):
    # 1. Track unclosed scopes and generate closers
    scope_stack = []  # parse namespace/section/end
    closers = [f"end {name}" for _, name in reversed(scope_stack) if name]

    # 2. Rename colliding simple names (no dots)
    rename_map = {}
    for match in re.finditer(r'^(?:theorem|def|lemma)\s+(\w+)', content, re.M):
        name = match.group(1)
        if '.' in name: continue  # skip Mathlib namespace extensions
        if name in all_names_seen:
            rename_map[name] = f"{name}_{i:02d}"
        all_names_seen.setdefault(name, 0)
        all_names_seen[name] += 1

    for old, new in rename_map.items():
        content = re.sub(r'\b' + re.escape(old) + r'\b', new, content)

    # 3. Wrap in section (scopes `open` statements)
    output += f"section FILE_{i:02d}\n{content}\n"
    output += '\n'.join(closers) + f"\nend FILE_{i:02d}\n"
```

**Critical: do NOT rename names containing dots** (like `Ideal.mem_iff_associated`).
Those extend existing Mathlib namespaces — renaming `Ideal` would break the
Mathlib type `Ideal R` everywhere in that file.

### 8. Final Verification

```bash
curl -s --max-time 300 -X POST $ENDPOINT --data-binary @combined.lean | \
  python3 -c "import sys,json; d=json.load(sys.stdin); \
  print(f'ok={d[\"ok\"]}, errors={len([m for m in d[\"messages\"] if m[\"severity\"]==\"error\"])}, sorries={len(d.get(\"sorries\",[]))}, elapsed={d[\"elapsed\"]:.1f}s')"
```

Target: **0 errors**. Sorries are acceptable only if intentional in the original.

## Textbooks Successfully Extracted

### Mathematics in Lean (MIL)
- **Repo**: `leanprover-community/mathematics_in_lean`
- **Lean version**: 4.21
- **Result**: 42/43 files pass → `mil-all.lean` (4,794 lines, 488 decls, 43s)
- **Key patches**: add_le_add swap, abs_add rename, Basis→Module.Basis, HasQuotient field rename, ≤₁ parens
- **Location**: `lean-frontend-cf/mil-all.lean`

### Formalising Mathematics 2024 (Kevin Buzzard)
- **Repo**: `ImperialCollegeLondon/formalising-mathematics-2024`
- **Lean version**: 4.5
- **Result**: 53/87 files pass → `fm-all.lean` (6,216 lines, 465 decls, 30s)
- **Key patches**: triv→trivial, inv_mul_self→inv_mul_cancel, peel tactic, cross-file TendsTo deps
- **34 skipped**: Sections 15-21 (advanced algebra, Galois theory) have deep API changes
- **Location**: `lean-frontend-cf/fm-all.lean`

### Competition Math (compfiles)
- **Repo**: `dwrensha/compfiles`
- **Lean version**: 4.28-rc1 (close to REPL version)
- **Result**: 162/241 complete problems pass → `compfiles-all.lean` (33,945 lines)
- **Key patches**: strip ProblemExtraction macros, problem→theorem, determine→def
- **Too large for single REPL request** — individual files verified
- **Location**: `lean-frontend-cf/compfiles-all.lean`

### Textbooks Evaluated but NOT Extracted

| Source | Reason |
|--------|--------|
| Theorem Proving in Lean 4 | Verso book system, not standalone .lean |
| The Mechanics of Proof (Macbeth) | Custom tactic library (addarith, numbers, cancel), disables standard tactics |
| How to Prove It with Lean | Custom HTPILib dependency, exercises use `done` not `sorry` |
| Natural Number Game (NNG4) | Game DSL (World/Level), not standard Lean |
| miniF2F | Lean 3 |

### Good Candidates NOT Yet Tried
- `leanprover-community/mathlib4` — Archive/ folder has formalized math (IMO, etc.)
- Hitchhiker's Guide to Logical Verification (if a Lean 4 version exists)
- Any new textbook using `import Mathlib.Tactic` without custom libraries

## Tips

1. **Start with the solution files**, not exercise files. Exercise files have intentional `sorry`s.
2. **Test individually first**, then concatenate. Debugging a 5000-line concatenated file is painful.
3. **Newer textbook = fewer patches needed.** compfiles (Lean 4.28) needed almost no patches vs MIL (4.21).
4. **The REPL is stateful** — if you hammer it with 200+ requests, it may need a moment. Space out batch tests.
5. **`set_option warningAsError false`** at the top of concatenated files silences deprecation warnings.
6. **Empty files** (imports only) need a trivial declaration: `example : True := trivial`
7. **Watch for `open` leakage** — this is the #1 source of errors in concatenated files.
8. **Don't rename dotted names** — `Ideal.foo` is extending Mathlib's `Ideal` namespace, not defining a new `Ideal`.
