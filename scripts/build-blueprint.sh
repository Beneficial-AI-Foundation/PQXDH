#!/usr/bin/env bash

set -euo pipefail

usage() {
  cat <<'EOF'
Usage: ./scripts/build-blueprint.sh [OUTPUT_ROOT]

Build the X3DH documentation blueprint artifacts.

Defaults:
  OUTPUT_ROOT = _out/blueprint

Artifacts:
  - pqxdhdocs (X3DH Protocol documentation)
EOF
}

case "${1:-}" in
  -h|--help)
    usage
    exit 0
    ;;
esac

if (( $# > 1 )); then
  usage >&2
  exit 1
fi

# Change to repo root
cd "$(dirname "$0")/.."

out_root="${1:-_out/blueprint}"
mkdir -p "$out_root"

echo "[build-blueprint] building pqxdhdocs executable"
lake build pqxdhdocs

echo "[build-blueprint] generating blueprint -> ${out_root}"
".lake/build/bin/pqxdhdocs" --output "$out_root"

echo "[build-blueprint] done"
echo "[build-blueprint] output:"
readlink -f "$out_root"
