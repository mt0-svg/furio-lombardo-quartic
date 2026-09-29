#!/bin/bash
# Builds the w7 data and check modules one at a time (lake build under the shared lock /tmp/furio-lean.lock and cap),
# then prints the axioms of every W7Check statement (code/selmer-local-conditions/w7_checks_axioms.lean).
# Usage: code/selmer-local-conditions/lean_build_w7.sh (from any directory); outputs code/selmer-local-conditions/lean_build_w7.out, w7_checks_axioms.out.
# Run in the workspace with each lake call under a resource cap (cap -m 7G -c 3).
set -eu
cd "$(dirname "$0")/../.."
out=$PWD/code/selmer-local-conditions/lean_build_w7.out
rm -f $out
echo "# lake build of the w7 data and check modules, $(date -u +%FT%TZ)" > $out
cd lean
for m in W7Data W7DataL W7DataN W7CheckM W7CheckL W7CheckN0 W7CheckN1 W7CheckN W7CheckB W7Check; do
  set +e
  /usr/bin/time -f "%e s wall, %M KB max RSS" -o /tmp/sp7_build_time flock /tmp/furio-lean.lock \
    lake build FurioLombardo.Discharge.SelmerBasis.$m > /tmp/sp7_build_log 2>&1
  rc=$?
  set -e
  echo "$m: rc=$rc, $(tail -1 /tmp/sp7_build_time)" >> $out
  grep -v "^✔\|^info: \|^⣿\|^\s*$" /tmp/sp7_build_log | tail -20 | sed 's/^/  /' >> $out
  if [ $rc != 0 ]; then echo "build of $m failed" >> $out; cat $out; exit 1; fi
done
set +e
/usr/bin/time -f "%e s wall, %M KB max RSS" -o /tmp/sp7_build_time lake env lean ../code/selmer-local-conditions/w7_checks_axioms.lean > ../code/selmer-local-conditions/w7_checks_axioms.out 2>&1
rc=$?
set -e
echo "w7_checks_axioms.lean: rc=$rc, $(tail -1 /tmp/sp7_build_time)" >> $out
cat $out
