#!/bin/sh
# class_number_minkowski_run.sh: all prime ideals of K21 of norm <= the Minkowski bound (40372280), in 8 disjoint ranges of primes,
# 4 processes at a time. The recorded runs ran in the workspace with each gp process under a resource cap
# (cap -m 1500M -c 1).
# Outputs are written outside the repository during the run and copied to class_number_minkowski_rangeK.out at the end:
# a commit made during the run can replace a tracked
# file by a new inode, and a running job then writes its last lines into the unlinked old one (lost run, 2026-09-26).
# (First run, without the integrality check: class_number_minkowski_first_range*.out.)
# Run from code/earlier-computations: sh class_number_minkowski_run.sh
W=5050000
TMP=/tmp/k21c/v2
mkdir -p $TMP
for k in 0 1 2 3 4 5 6 7; do echo $k; done | xargs -P 4 -I K sh -c "LO=\$((K * $W)) HI=\$(((K + 1) * $W)) gp -q class_number_minkowski.gp < /dev/null > $TMP/rK.out 2>&1"
for k in 0 1 2 3 4 5 6 7; do cp $TMP/r$k.out class_number_minkowski_range$k.out; done
grep -h "^range\|RESULT\|FAILED\|error" class_number_minkowski_range*.out
