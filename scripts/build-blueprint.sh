#!/usr/bin/env bash

set -euo pipefail

usage() {
  cat <<'EOF'
Usage: ./scripts/build-blueprint.sh [OUTPUT_ROOT]

Build the X3DH documentation blueprint artifacts.

Defaults:
  OUTPUT_ROOT = _out/blueprint

Artifacts:
  - docs (X3DH Protocol documentation)
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

echo "[build-blueprint] building docs executable"
lake -d docs build docs

echo "[build-blueprint] generating blueprint -> ${out_root}"
"docs/.lake/build/bin/docs" --output "$out_root"

echo "[build-blueprint] adding Lean syntax highlighting"
node --experimental-vm-modules scripts/highlight-lean.mjs "$out_root" || echo "[build-blueprint] warning: syntax highlighting failed (node/shiki not available)"

echo "[build-blueprint] done"
echo "[build-blueprint] output:"
readlink -f "$out_root"
echo ""
echo "To serve the documentation locally:"
echo "  python3 -m http.server 8080 -d $out_root"
echo ""
echo "Then open http://localhost:8080 in your browser."
