#!/usr/bin/env bash
# Compile one Lean file of M3b inside the Lean project lean/, memory capped (no swap).
# Usage: code/selmer-global-bound/lean_check_chevalley.sh lean/FurioLombardo/M3b/File.lean   (path relative to the repository root)
set -euo pipefail
here="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$here/lean"
f="${1#lean/}"
exec systemd-run --user --scope --quiet -p MemoryMax=10G -p MemorySwapMax=0 nice -n 10 lake env lean "$f"
