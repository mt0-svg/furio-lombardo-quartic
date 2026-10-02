#!/bin/sh
# Rerun the Sage second implementations (code/README.md, Rerunning, items 5 to 7) and compare each output with its
# recorded one. The times the programs print ("1.9s", "time 2.0s") depend on the machine and are blanked on both
# sides before the comparison; everything else must be identical. Last check: the text data files the programs
# write again (centres, box bounds) are identical to the shipped ones.
# Usage, from the root of the repository: sh code/second-implementations/rerun.sh
# SAVE=dir writes the output of each check to dir/sage/<name>.txt and its result line to dir/results/sage_<name>.tsv.
set -u
root=$(pwd)
here=$root/code/second-implementations
save=${SAVE:-}
[ -n "$save" ] && mkdir -p "$save/sage" "$save/results"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
fail=0

blank_times() { sed -E 's/[0-9]+(\.[0-9]+)?s\b/<time>/g' "$1"; }

record() { # name command seconds result
  printf 'sage %s\t%s\t%s s\t%s\tsage/%s.txt\n' "$1" "$2" "$3" "$4" "$1"
  [ -z "$save" ] || printf 'sage %s\t%s\t%s s\t%s\tsage/%s.txt\n' "$1" "$2" "$3" "$4" "$1" > "$save/results/sage_$1.tsv"
}

# check NAME DIR RECORDED ARGS...: run sage ARGS in DIR, compare with DIR/RECORDED ("-": no recorded output, the
# check is the exit status; the run writes files that later checks read).
check() {
  name=$1 dir=$2 rec=$3
  shift 3
  s=$(date +%s)
  (cd "$here/$dir" && sage "$@") > "$tmp/$name.txt" 2>&1
  rc=$?
  secs=$(($(date +%s) - s))
  [ -z "$save" ] || cp "$tmp/$name.txt" "$save/sage/$name.txt"
  blank_times "$tmp/$name.txt" > "$tmp/$name.blank"
  if [ "$rc" -ne 0 ]; then
    r="FAIL, exit $rc"
  elif [ "$rec" = - ]; then
    r="PASS, exit 0 (no recorded output)"
  elif blank_times "$here/$dir/$rec" | diff - "$tmp/$name.blank" > "$tmp/$name.diff"; then
    r="PASS, identical to $dir/$rec (times blanked)"
  else
    r="FAIL, different from $dir/$rec"
    head -40 "$tmp/$name.diff"
  fi
  case $r in FAIL*) fail=1 ;; esac
  record "$name" "sage $* (in code/second-implementations/$dir)" "$secs" "$r"
}

# The shipped text data that the local-group-covering programs write again.
data="local-group-covering/centres_twist0_prec400.txt local-group-covering/centres_twist1_prec400.txt
local-group-covering/centres_twist0_prec1000.txt local-group-covering/centres_twist1_prec1000.txt
local-group-covering/box_bounds_twist0.txt local-group-covering/box_bounds_twist1.txt"
mkdir "$tmp/shipped"
for f in $data; do cp "$here/$f" "$tmp/shipped/$(echo "$f" | tr / _)"; done

check selmer_space selmer-space selmer_space_check.out selmer_space_check.sage
check sigma selmer-space sigma_check.out sigma_check.sage
check field_and_bruin_identity descent-set field_and_bruin_identity.out field_and_bruin_identity.sage
check support_determinant descent-set support_determinant.out support_determinant.sage
check sunits_basis descent-set sunits_basis.out sunits_basis.sage
check good_prime_sieve descent-set good_prime_sieve.out good_prime_sieve.sage
check local_conditions_2_3 descent-set local_conditions_2_3.out local_conditions_2_3.sage
check final_classes descent-set final_classes.out final_classes.sage
check coverings_kat descent-set coverings_kat.out coverings_kat.sage
check logs_prec400 local-group-covering - logs.sage 400
check logs_prec1000 local-group-covering logs_prec1000.out logs.sage 1000
check lattice local-group-covering lattice.out lattice.sage
check centres_prec400 local-group-covering centres_prec400.out centres.sage 400
check centres_prec1000 local-group-covering centres_prec1000.out centres.sage 1000
check box_bounds local-group-covering box_bounds.out box_bounds.sage
check compare_certs local-group-covering compare_certs.out compare_certs.sage
check compare_lattice_basis local-group-covering compare_lattice_basis.out compare_lattice_basis.sage
check precision_check local-group-covering precision_check.out precision_check.sage
check abel_prym_kat local-group-covering abel_prym_kat.out abel_prym_kat.sage 1000 3
check pullback_kat local-group-covering pullback_kat.out pullback_kat.sage

n=0 bad=""
for f in $data; do
  n=$((n + 1))
  cmp -s "$here/$f" "$tmp/shipped/$(echo "$f" | tr / _)" || bad="$bad $f"
done
{ echo "Text data written again by the local-group-covering programs, against the shipped files:"; for f in $data; do echo "  $f"; done
  if [ -z "$bad" ]; then echo "all $n identical"; else echo "different:$bad"; fi; } > "$tmp/data_files.txt"
[ -z "$save" ] || cp "$tmp/data_files.txt" "$save/sage/data_files.txt"
if [ -z "$bad" ]; then r="PASS, $n files identical"; else r="FAIL, different:$bad"; fail=1; fi
record data_files "cmp of the $n text data files written again with the shipped ones" 0 "$r"
exit $fail
