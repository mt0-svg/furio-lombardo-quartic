#!/usr/bin/env bash
# Split a generated Lean data file into parts under the 500 KB commit limit.
#
# usage: split_lean_data.sh DIR NAME MODPREFIX [MAXBYTES]
#   DIR/NAME.lean is a generated file of the form
#     import ...            (one or more lines)
#     /-! docstring -/
#     namespace N
#     open ...
#     <top-level declarations, each starting with `def` or a `/--` docstring>
#     end N
#   It is rewritten as DIR/NAMEP1.lean .. DIR/NAMEPk.lean (P1 keeps the original imports, Pi imports
#   P(i-1)), each with the same namespace and open lines, and DIR/NAME.lean keeps the docstring and
#   imports the last part, so every importer of NAME sees the same declarations.
#   MODPREFIX is the module path of DIR, e.g. FurioLombardo.Discharge.SelmerBasis.
# Cuts are made only before a line starting with `def ` that does not follow a docstring, or before
# a line starting with `/--`.
set -euo pipefail
dir=$1; name=$2; pre=$3; max=${4:-450000}
src="$dir/$name.lean"
tmp=$(mktemp -d)
awk -v tmp="$tmp" -v max="$max" '
  BEGIN { state = "head"; part = 1; sz = 0 }
  state == "head" {
    if ($0 ~ /^import /) { imports = imports $0 "\n"; next }
    if ($0 ~ /^namespace /) { ns = $0; next }
    if ($0 ~ /^open /) { op = op $0 "\n"; state = "body"; next }
    doc = doc $0 "\n"; next
  }
  state == "body" {
    if ($0 ~ /^end /) { endl = $0; next }
    cut = ($0 ~ /^\/--/) || ($0 ~ /^def / && prev !~ /-\/$/)
    if (cut && sz > max) { part++; sz = 0 }
    f = tmp "/body" part
    print $0 >> f
    sz += length($0) + 1
    prev = $0
  }
  END {
    printf "%s", imports > (tmp "/imports")
    printf "%s", doc > (tmp "/doc")
    print ns > (tmp "/ns"); printf "%s", op > (tmp "/open"); print endl > (tmp "/end")
    print part > (tmp "/nparts")
  }' "$src"
n=$(cat "$tmp/nparts")
for i in $(seq 1 "$n"); do
  out="$dir/${name}P$i.lean"
  {
    if [ "$i" -eq 1 ]; then cat "$tmp/imports"; else echo "import $pre.${name}P$((i - 1))"; fi
    echo
    echo "/-! Part $i of $n of \`$name\` (split by code/selmer-local-conditions/split_lean_data.sh). -/"
    echo
    cat "$tmp/ns"
    echo
    cat "$tmp/open"
    echo
    cat "$tmp/body$i"
    echo
    cat "$tmp/end"
  } > "$out"
done
{
  echo "import $pre.${name}P$n"
  cat "$tmp/doc"
} | sed -e :a -e '/^\n*$/{$d;N;ba' -e '}' > "$src"
rm -r "$tmp"
wc -c "$dir/$name.lean" "$dir/${name}"P*.lean
