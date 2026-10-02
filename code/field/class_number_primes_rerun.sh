#!/bin/sh
# Rerun class_number_primes.gp into a scratch directory, compare the generated blocks with the committed
# P000.lean .. P119.lean of FurioLombardo/M2/Data in the Lean package, and count the records.
# Needs field_bnf.bin (class_group_search.gp). Run from anywhere:
#   sh code/field/class_number_primes_rerun.sh > .../class_number_primes_rerun.out 2>&1
# Exit status 1 if the generated blocks differ from the committed ones.
cd "$(dirname "$0")" || exit 1
out=$(mktemp -d)
status=0
G5OUT="$out/" gp -q class_number_primes.gp < /dev/null
data=../../FurioLombardo/M2/Data
echo "generated files: $(ls "$out" | wc -l); committed files: $(ls "$data"/P*.lean | wc -l)"
if diff -r -q "$out" "$data" > "$out.diff"; then
  echo "diff -r against the committed blocks: identical"
else
  echo "diff -r against the committed blocks: DIFFERENT"; cat "$out.diff"; status=1
fi
n=$(cat "$data"/P*.lean | grep -c '^theorem c[0-9]')
bytes=$(cat "$data"/P*.lean | wc -c)
echo "records (theorem c<p>) in the committed blocks: $n; bytes: $bytes, $((bytes / n)) per record"
rm -rf "$out" "$out.diff"
exit $status
