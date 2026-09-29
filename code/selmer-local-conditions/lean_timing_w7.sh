#!/bin/bash
# Elaboration and kernel time of each w7 check module, by `lake env lean` on the source (no olean written, no lock;
# the lock waits make the lake build times of lean_build_w7.out useless as timings). The data-only baseline is
# probe_base of kernel_probe_w7.out (7.8 s, 7.0 GB, the mapped Mathlib oleans included).
# Usage: code/selmer-local-conditions/lean_timing_w7.sh (from any directory, after lean_build_w7.sh); output code/selmer-local-conditions/lean_timing_w7.out.
# Run in the workspace with each lake call under a resource cap (cap -m 7G -c 3).
set -eu
cd "$(dirname "$0")/../.."
out=$PWD/code/selmer-local-conditions/lean_timing_w7.out
rm -f $out
echo "# lake env lean on the w7 check modules, $(date -u +%FT%TZ), $(nproc) cores, cap -m 7G -c 3" > $out
cd lean
for m in W7CheckM W7CheckL W7CheckN0 W7CheckN1 W7CheckN W7CheckB W7Check; do
  set +e
  /usr/bin/time -f "%e s wall, %U s user, %M KB max RSS" -o /tmp/sp7_time lake env lean FurioLombardo/Discharge/SelmerBasis/$m.lean > /tmp/sp7_timing_log 2>&1
  rc=$?
  set -e
  echo "$m: rc=$rc, $(tail -1 /tmp/sp7_time)" >> $out
  sed 's/^/  /' /tmp/sp7_timing_log >> $out
done
cat $out
