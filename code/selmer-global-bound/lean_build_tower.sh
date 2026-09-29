#!/usr/bin/env bash
# Build modules of the M3b discharge (and their imports) in the Lean project lean/, memory capped (no swap).
# Usage: code/selmer-global-bound/lean_build_tower.sh FurioLombardo.Discharge.M3b.Module ...   (run from anywhere)
set -euo pipefail
here="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$here/lean"
exec systemd-run --user --scope --quiet -p MemoryMax=10G -p MemorySwapMax=0 nice -n 10 lake build "$@"
