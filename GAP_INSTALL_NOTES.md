# GAP installation notes

## Source + build steps (from https://www.gap-system.org/install/)

1. Download the GAP 4.15.1 source tarball.

   ```sh
   mkdir -p gap-src
   curl -fsSL https://github.com/gap-system/gap/releases/download/v4.15.1/gap-4.15.1.tar.gz \
     -o gap-src/gap-4.15.1.tar.gz
   ```

2. Extract the archive.

   ```sh
   tar -xzf gap-src/gap-4.15.1.tar.gz -C gap-src
   ```

3. Configure the build.

   ```sh
   cd gap-src/gap-4.15.1
   ./configure
   ```

4. Build GAP.

   ```sh
   make -j2
   ```

## Verification

Run GAP and compute a simple expression to confirm it starts correctly:

```sh
cd gap-src/gap-4.15.1
./gap -q <<'EOF'
3^80;
QUIT;
EOF
```

Expected output:

```
147808829414345923316083210206383297601
```
