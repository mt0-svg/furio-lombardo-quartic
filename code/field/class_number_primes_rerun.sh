#!/bin/sh
# Rerun class_number_primes.gp into a scratch directory, compare the generated blocks with the committed
# lean/FurioLombardo/M2/Data/P000.lean .. P119.lean and count the records.
# Needs field_bnf.bin (class_group_search.gp). Run from anywhere:
#   sh code/field/class_number_primes_rerun.sh > .../class_number_primes_rerun.out 2>&1
cd "$(dirname "$0")" || exit 1
out=$(mktemp -d)
G5OUT="$out/" gp -q class_number_primes.gp < /dev/null
data=../../../FurioLombardo/M2/Data
echo "generated files: $(ls "$out" | wc -l); committed files: $(ls "$data"/P*.lean | wc -l)"
if diff -r -q "$out" "$data" > "$out.diff"; then
  echo "diff -r against lean/FurioLombardo/M2/Data: identical"
else
  echo "diff -r against lean/FurioLombardo/M2/Data: DIFFERENT"; cat "$out.diff"
fi
n=$(cat "$data"/P*.lean | grep -c '^theorem c[0-9]')
bytes=$(cat "$data"/P*.lean | wc -c)
echo "records (theorem c<p>) in the committed blocks: $n; bytes: $bytes, $((bytes / n)) per record"
rm -rf "$out" "$out.diff"
