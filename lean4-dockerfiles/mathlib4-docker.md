# Running Lean 4 with Mathlib via Docker

## Quick Start

Run a Lean command with Mathlib available:

```bash
docker run --rm lixuanji/mathlib4:v4.24.0 bash -c '
  cd /project &&
  echo -e "import Mathlib\n#check Real" > MathProject.lean &&
  lake env lean MathProject.lean'
```

## Details

The image `lixuanji/mathlib4:v4.24.0` contains a lake project at `/project` with precompiled Mathlib oleans. To run custom Lean code:

1. Write your Lean source to `/project/MathProject.lean`
2. Run it with `lake env lean MathProject.lean`

Example with `#eval`:

```bash
docker run --rm lixuanji/mathlib4:v4.24.0 bash -c '
  cd /project &&
  echo "#eval 1+1" > MathProject.lean &&
  lake env lean MathProject.lean'
```

A typical run takes ~9 seconds including container startup.
