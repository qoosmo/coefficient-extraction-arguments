#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT/rust"
if [ ! -f Cargo.toml ]; then
  echo "Rust scaffold only: Cargo workspace will be added with the executable protocol specification."
  exit 0
fi
cargo test --release
