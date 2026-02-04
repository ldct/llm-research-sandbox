# Lean 4 Docker Images

Pre-built Docker images for Lean 4 theorem prover.

## Available Tags

| Tag | Lean Version |
|-----|--------------|
| `lixuanji/lean4:v4.24.0` | 4.24.0 |
| `lixuanji/lean4:v4.24.1` | 4.24.1 |
| `lixuanji/lean4:v4.25.0` | 4.25.0 |
| `lixuanji/lean4:v4.25.1` | 4.25.1 |
| `lixuanji/lean4:v4.25.2` | 4.25.2 |
| `lixuanji/lean4:v4.26.0` | 4.26.0 |
| `lixuanji/lean4:v4.27.0` | 4.27.0 |
| `lixuanji/lean4:v4.28.0-rc1` | 4.28.0-rc1 |

## Usage

### Pull an image

```bash
docker pull lixuanji/lean4:v4.27.0
```

### Run interactively

```bash
docker run -it lixuanji/lean4:v4.27.0
```

### Evaluate Lean code

```bash
echo '#eval 1 + 1' | docker run -i lixuanji/lean4:v4.27.0 lean --stdin
```

### Mount a local directory

```bash
docker run -it -v $(pwd):/work -w /work lixuanji/lean4:v4.27.0
```

### Check a Lean file

```bash
docker run -v $(pwd):/work -w /work lixuanji/lean4:v4.27.0 lean MyFile.lean
```

## Building from Dockerfiles

To build an image locally:

```bash
docker build -f Dockerfile.lean4-27.0 -t lean4:v4.27.0 .
```

## Base Image

All images are based on `ubuntu:noble` (Ubuntu 24.04 LTS).
