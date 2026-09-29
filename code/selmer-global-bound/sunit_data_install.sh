#!/usr/bin/env bash
# sunit_data_install.sh: installs the candidate SUnitData.lean that sunit_data_lean.gp wrote
# and rechecked, only if (1) sunit_data_lean.out is a passing run, (2) the candidate is the file it checked (sha256),
# (3) the candidate compiles alone, and then (4) builds FurioLombardo.Discharge.SelmerBasis.SUnitDefs on it; if that
# build fails, the previous committed SUnitData.lean is restored.
# Run from the repository root:
#   code/selmer-global-bound/sunit_data_install.sh > code/selmer-global-bound/sunit_data_install.out 2>&1
# Run in the workspace under a resource cap (cap -m 4G -c 1, -t 10min for the compile and -t 20min for the build).
set -u
cd "$(git rev-parse --show-toplevel)" || exit 1
dir=problems/furio-lombardo-quartic
cand=/tmp/sb5/SUnitData.cand.lean
dst=$dir/lean/FurioLombardo/Discharge/SelmerBasis/SUnitData.lean
out=$dir/code/selmer-global-bound/sunit_data_lean.out
grep -q '^DONE sunit_data_lean: [0-9]* checks passed, 0 failed' "$out" || { echo "FAIL: sunit_data_lean.out is not a passing run"; exit 1; }
echo "ok: $(grep '^DONE sunit_data_lean' "$out")"
want=$(grep '^candidate sha256' "$out" | awk '{print $3}')
have=$(sha256sum "$cand" | awk '{print $1}')
[ -n "$want" ] && [ "$want" = "$have" ] || { echo "FAIL: the candidate is not the file sunit_data_lean.gp checked"; exit 1; }
echo "ok: the candidate is the file checked by sunit_data_lean.gp (sha256 $have)"
t0=$(date +%s)
flock /tmp/furio-sbglobal.lock bash -c "cd $dir/lean && lake env lean $cand" || { echo "FAIL: the candidate does not compile"; exit 1; }
echo "ok: the candidate compiles alone (lake env lean, $(($(date +%s) - t0)) s wall)"
cp "$cand" "$dst"
[ "$(sha256sum < "$dst" | awk '{print $1}')" = "$have" ] || { echo "FAIL: the installed file differs from the candidate"; exit 1; }
echo "ok: installed $dst (sha256 $have)"
t0=$(date +%s)
if (cd $dir/lean && flock /tmp/furio-sbglobal.lock flock /tmp/furio-lake.lock lake build FurioLombardo.Discharge.SelmerBasis.SUnitDefs); then
  echo "ok: lake build FurioLombardo.Discharge.SelmerBasis.SUnitDefs ($(($(date +%s) - t0)) s wall)"
else
  git show "HEAD:$dst" > "$dst"
  echo "FAIL: lake build FurioLombardo.Discharge.SelmerBasis.SUnitDefs; the committed SUnitData.lean is restored"
  exit 1
fi
echo "DONE sunit_data_install"
