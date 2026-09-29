#!/bin/bash
# Builds W7Place (lake build under the shared lock /tmp/furio-lean.lock and cap), prints the axioms of every theorem of the
# files (code/selmer-local-conditions/w7_place_axioms.lean) and the sorry-leaves of coordCond_w7 (sorry-leaves, a workspace tool outside this repository).
# Usage: code/selmer-local-conditions/final_check_w7.sh (from any directory); outputs code/selmer-local-conditions/final_check_w7.out, w7_place_axioms.out.
# Run in the workspace with each lake call under a resource cap (cap -m 7G -c 3).
set -eu
cd "$(dirname "$0")/../.."
out=$PWD/code/selmer-local-conditions/final_check_w7.out
echo "# final check of lane selmer-local-conditions, $(date -u +%FT%TZ), commit $(git rev-parse --short HEAD)" > $out
cd lean
set +e
/usr/bin/time -f "%e s wall, %M KB max RSS" -o /tmp/sp7_final_time flock /tmp/furio-lean.lock \
  lake build FurioLombardo.Discharge.SelmerBasis.W7Place > /tmp/sp7_final_log 2>&1
rc=$?
set -e
echo "lake build W7Place: rc=$rc, $(tail -1 /tmp/sp7_final_time)" >> $out
grep -E "error|declaration uses 'sorry'|Build completed" /tmp/sp7_final_log | sed 's/^/  /' >> $out || true
if [ $rc != 0 ]; then cat $out; exit 1; fi
set +e
lake env lean ../code/selmer-local-conditions/w7_place_axioms.lean > ../code/selmer-local-conditions/w7_place_axioms.out 2>&1
echo "w7_place_axioms.lean: rc=$?, $(grep -c "depends on axioms" ../code/selmer-local-conditions/w7_place_axioms.out) axiom lines, \
$(grep -c "does not depend on any axioms" ../code/selmer-local-conditions/w7_place_axioms.out) without axioms, \
$(grep -c "sorryAx" ../code/selmer-local-conditions/w7_place_axioms.out) with sorryAx, \
$(grep -c "Lean.ofReduceBool\|Lean.trustCompiler" ../code/selmer-local-conditions/w7_place_axioms.out) with ofReduceBool or trustCompiler" >> $out
echo "sorry-leaves of FurioLombardo.Discharge.SelmerBasis.W7.coordCond_w7:" >> $out
# sorry-leaves: a tool of the workspace this record was run in, not shipped here
sorry-leaves . FurioLombardo.Discharge.SelmerBasis.W7Place \
  FurioLombardo.Discharge.SelmerBasis.W7.coordCond_w7 >> $out 2>&1
echo "sorry-leaves rc=$?" >> $out
set -e
cat $out
