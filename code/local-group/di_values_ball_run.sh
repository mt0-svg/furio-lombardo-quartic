#!/bin/bash
# di_values_ball_run.sh P K I C: the kv_d2 probe at P bits. The #eval pass on all 14 points (di_values_ball_eval_prec<P>.out), then the kernel
# pass on point (K, I) in chunks of C steps (C = 0: #eval pass only) (di_values_ball_kernel_prec<P>_twist<K>_d<I>.lean, .out). Run from this directory.
set -euo pipefail
P=$1; K=$2; I=$3; C=$4
# Run in the workspace under a resource cap and a lock shared by the Lean jobs: each lake command below ran as
# cap -m 2G -c 1 -t 20min flock /tmp/furio-lake.lock lake env lean ... (-t 30min for the kernel pass).
HERE=$(pwd)
LEAN=$HERE/../..
mkdir -p /tmp/kvd2
sed "s/@P@/$P/g" di_values_ball_head.lean.in > /tmp/kvd2/head.lean
{
  cat /tmp/kvd2/head.lean di_values_ball_data.lean di_values_ball_prog.lean di_values_ball_eval.lean.in
  for k in 0 1; do for i in 1 2 3 4 5 6 7; do
    echo "#eval probe \"k$k D_$i\" $k f_$k D_${k}_$i E0_$k J_${k}_$i tJ_${k}_$i err_${k}_$i"
  done; done
} > di_values_ball_eval_prec$P.lean
( cd $LEAN && lake env lean -j1 ../code/local-group/di_values_ball_eval_prec$P.lean ) > di_values_ball_eval_prec$P.out 2>&1
cat di_values_ball_eval_prec$P.out
[ "$C" = 0 ] && exit 0
{
  cat /tmp/kvd2/head.lean di_values_ball_data.lean di_values_ball_prog.lean di_values_ball_eval.lean.in
  echo "#eval emit \"f_$K\" \"D_${K}_$I\" \"E0_$K\" f_$K D_${K}_$I E0_$K J_${K}_$I $C"
} > /tmp/kvd2/emit.lean
( cd $LEAN && lake env lean -j1 /tmp/kvd2/emit.lean ) > /tmp/kvd2/emit.out 2>&1
KF=di_values_ball_kernel_prec${P}_twist${K}_d$I.lean
{
  cat /tmp/kvd2/head.lean
  echo "set_option profiler true"
  echo "set_option profiler.threshold 10"
  echo "set_option Elab.async false"
  cat di_values_ball_data.lean di_values_ball_prog.lean
  echo
  cat /tmp/kvd2/emit.out
} > $KF
( cd $LEAN && /usr/bin/time -v lake env lean -j1 ../code/local-group/$KF ) > ${KF%.lean}.out 2>&1
grep -c "type checking took" ${KF%.lean}.out || true
