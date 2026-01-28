#!/usr/bin/env bash
set -euo pipefail

GAP_VERSION="4.15.1"
GAP_DIR="gap-src"
GAP_TARBALL="gap-${GAP_VERSION}.tar.gz"
GAP_URL="https://github.com/gap-system/gap/releases/download/v${GAP_VERSION}/${GAP_TARBALL}"
GAP_BUILD_DIR="${GAP_DIR}/gap-${GAP_VERSION}"

mkdir -p "${GAP_DIR}"

if [[ ! -f "${GAP_DIR}/${GAP_TARBALL}" ]]; then
  curl -fsSL "${GAP_URL}" -o "${GAP_DIR}/${GAP_TARBALL}"
fi

tar -xzf "${GAP_DIR}/${GAP_TARBALL}" -C "${GAP_DIR}"

pushd "${GAP_BUILD_DIR}" > /dev/null
./configure
make -j2

OUTPUT=$(./gap -q <<'EOF_GAP'
3^80;
QUIT;
EOF_GAP
)

EXPECTED="147808829414345923316083210206383297601"
if [[ "${OUTPUT}" != "${EXPECTED}" ]]; then
  echo "GAP verification failed."
  echo "Expected: ${EXPECTED}"
  echo "Got: ${OUTPUT}"
  exit 1
fi

echo "GAP install verified."

popd > /dev/null
