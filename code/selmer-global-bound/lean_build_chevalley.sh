#!/usr/bin/env bash
# Build one module of M3b (and its imports) in the Lean project lean/, memory capped (no swap).
# Usage: code/selmer-global-bound/lean_build_chevalley.sh FurioLombardo.M3b.Module   (run from anywhere)
set -euo pipefail
here="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$here/lean"
exec systemd-run --user --scope --quiet -p MemoryMax=10G -p MemorySwapMax=0 nice -n 10 lake build "$@"
