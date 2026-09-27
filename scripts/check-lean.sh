#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT/lean"

if grep -R -nE '\b(sorry|admit|axiom)\b' CoeffExtract CoeffExtract.lean; then
  echo "Forbidden Lean placeholder/axiom found." >&2
  exit 1
fi

lake build
lake env lean AxiomAudit.lean
