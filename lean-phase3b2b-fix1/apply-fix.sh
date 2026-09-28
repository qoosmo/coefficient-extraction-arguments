#!/usr/bin/env bash
set -euo pipefail
REPO="${1:-$HOME/Downloads/coefficient-extraction-arguments-lean1}"
cp "$(dirname "$0")/lean/CoeffExtract/MLEProductBridge.lean" \
  "$REPO/lean/CoeffExtract/MLEProductBridge.lean"
echo "Lean Phase 3B2B fix 1 applied."
echo "Run: ./scripts/check-lean.sh"
