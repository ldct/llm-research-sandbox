# Docker Image Test One-Liners

## ghcr.io/ldct/lean4

```bash
docker run --rm ghcr.io/ldct/lean4:v4.24 lean --version
docker run --rm ghcr.io/ldct/lean4:v4.24.1 lean --version
docker run --rm ghcr.io/ldct/lean4:v4.25.0 lean --version
docker run --rm ghcr.io/ldct/lean4:v4.25.1 lean --version
docker run --rm ghcr.io/ldct/lean4:v4.25.2 lean --version
docker run --rm ghcr.io/ldct/lean4:v4.26.0 lean --version
docker run --rm ghcr.io/ldct/lean4:v4.27 lean --version
docker run --rm ghcr.io/ldct/lean4:v4.27.0 lean --version
docker run --rm ghcr.io/ldct/lean4:v4.28.0-rc1 lean --version
```

## ghcr.io/ldct/mathlib4

```bash
docker run --rm ghcr.io/ldct/mathlib4:v4.24.0 bash -c 'cd /project && lake env lean -c "import Mathlib" && echo ok'
docker run --rm ghcr.io/ldct/mathlib4:v4.25.0 bash -c 'cd /project && lake env lean -c "import Mathlib" && echo ok'
docker run --rm ghcr.io/ldct/mathlib4:v4.26.0 bash -c 'cd /project && lake env lean -c "import Mathlib" && echo ok'
docker run --rm ghcr.io/ldct/mathlib4:v4.27.0 bash -c 'cd /project && lake env lean -c "import Mathlib" && echo ok'
```

## ghcr.io/ldct/canonical-lean

```bash
docker run --rm ghcr.io/ldct/canonical-lean:latest bash -c 'cd /canonical && echo "import Canonical" > T.lean && echo "example : Nat := by canonical" >> T.lean && lake build T 2>&1 | tail -1'
```

## ghcr.io/ldct/mathlib4-canonical

```bash
docker run --rm ghcr.io/ldct/mathlib4-canonical:v4.27.0-rc1 bash -c 'cd /project && echo "import Mathlib" > T.lean && echo "import Canonical" >> T.lean && echo "example : Nat := by canonical" >> T.lean && echo "example : 1 + 1 = 2 := by norm_num" >> T.lean && lake build T 2>&1 | tail -1'
```

## ghcr.io/ldct/cslib

```bash
docker run --rm ghcr.io/ldct/cslib:v4.25.0 bash -c 'cd /project && lake env lean -c "import Cslib" && echo ok'
docker run --rm ghcr.io/ldct/cslib:v4.26.0 bash -c 'cd /project && lake env lean -c "import Cslib" && echo ok'
docker run --rm ghcr.io/ldct/cslib:v4.27.0-rc1 bash -c 'cd /project && lake env lean -c "import Cslib" && echo ok'
```
