#!/bin/bash
# The Lean sources of the recorded runs (the clean build of clean_build.out and the Comparator timing of
# comparator_time.out, both on the tree of tag v1.1.0) against the Lean sources of this version, comments removed.
#   1. The raw hash of the FurioLombardo .lean files of REV (default v1.1.0), Challenge.lean and Solution.lean left
#      out, computed as clean_build.sh computes it, against the FurioLombardo hash of the clean_build.out header.
#   2. Each .lean file of FurioLombardo/ in REV and in the working tree, with comments removed: line comments `--`,
#      nested block comments `/- ... -/` (docstrings `/--` and `/-!` included) replaced by one space, string and char
#      literals lexed so that a `--` or `/-` inside them is code; blank lines and trailing blanks dropped. Prints
#      every file whose code differs or that is only on one side, the number of files whose raw text differs, and
#      one sha256 of the whole stripped tree on each side (the sha256sum listing of the stripped files, as in step 1).
#   3. Controls: pairs of small texts whose comments differ (same code) and whose code differs, and one file of
#      the tree with a code edit and with a comment edit.
# Usage: code/formal-proof/comment_only_build_sources.sh [REV], from any directory; reads REV from the git history
# of the repository. Output as in comment_only_build_sources.out.
set -euo pipefail
export LC_ALL=C
here=$(cd "$(dirname "$0")" && pwd)
if [ -f "$here/../../lakefile.toml" ]; then pkg=$(cd "$here/../.." && pwd); else pkg=$(cd "$here/../../lean" && pwd); fi
cd "$pkg"
rev=${1:-v1.1.0}
commit=$(git rev-parse --verify "$rev^{commit}")
t=$(mktemp -d); trap 'rm -rf "$t"' EXIT

lex='
{
  co = ""; n = length($0); i = 1
  if (st == "line") st = ""
  while (i <= n) {
    c = substr($0, i, 1); c2 = substr($0, i, 2)
    if (st == "block") {
      if (c2 == "/-") { depth++; i += 2; continue }
      if (c2 == "-/") { depth--; i += 2; if (depth == 0) { st = ""; co = co " " }; continue }
      i++; continue
    }
    if (st == "str") {
      co = co c
      if (c == "\\") { co = co substr($0, i + 1, 1); i += 2; continue }
      if (c == "\"") st = ""
      i++; continue
    }
    if (c2 == "--") { st = "line"; break }
    if (c2 == "/-") { st = "block"; depth = 1; i += 2; continue }
    if (c == "\"") { st = "str"; co = co c; i++; continue }
    if (c == "\x27" && substr($0, i, 3) == "\x27\"\x27") { co = co substr($0, i, 3); i += 3; continue }
    if (c == "\x27" && substr($0, i, 4) == "\x27\\\"\x27") { co = co substr($0, i, 4); i += 4; continue }
    co = co c; i++
  }
  sub(/[ \t]+$/, "", co); if (co != "") print co
}'
strip() { awk "$lex"; }

echo "# comment_only_build_sources.sh: $rev = commit $commit"

# 1. raw hash of REV, as clean_build.sh computes it
git ls-tree -r --name-only "$commit" -- FurioLombardo | grep '\.lean$' | sort > "$t/old"
find FurioLombardo -name '*.lean' -type f | sort > "$t/new"
grep -vxE 'FurioLombardo/(Challenge|Solution)\.lean' "$t/old" > "$t/old-build"
while read -r f; do printf '%s  %s\n' "$(git show "$commit:$f" | sha256sum | cut -c1-64)" "$f"; done < "$t/old-build" \
  | sha256sum | cut -c1-64 > "$t/rawhash"
rec=$(sed -n 's/^# package: .*; FurioLombardo \([0-9a-f]\{64\}\),.*/\1/p' "$here/clean_build.out" | sort -u)
echo "1. raw FurioLombardo hash of $rev without Challenge.lean and Solution.lean ($(wc -l < "$t/old-build") files): $(cat "$t/rawhash")"
echo "   FurioLombardo hash of the clean_build.out headers: $rec"
if [ "$(cat "$t/rawhash")" = "$rec" ]; then echo "   equal: the clean build ran on these sources"; else echo "   DIFFERENT"; fi

# 2. stripped comparison, every .lean file of FurioLombardo/
echo "2. code of $rev against the working tree, comments removed"
only_old=$(comm -23 "$t/old" "$t/new"); only_new=$(comm -13 "$t/old" "$t/new")
[ -z "$only_old" ] || printf '   only in %s: %s\n' "$rev" $only_old
[ -z "$only_new" ] || printf '   only in the working tree: %s\n' $only_new
nraw=0; ncode=0; nboth=0
: > "$t/list-old"; : > "$t/list-new"
while read -r f; do
  nboth=$((nboth + 1))
  git show "$commit:$f" > "$t/a"
  cmp -s "$t/a" "$f" || nraw=$((nraw + 1))
  strip < "$t/a" > "$t/sa"; strip < "$f" > "$t/sb"
  printf '%s  %s\n' "$(sha256sum < "$t/sa" | cut -c1-64)" "$f" >> "$t/list-old"
  printf '%s  %s\n' "$(sha256sum < "$t/sb" | cut -c1-64)" "$f" >> "$t/list-new"
  if ! cmp -s "$t/sa" "$t/sb"; then ncode=$((ncode + 1)); echo "   code differs: $f"; fi
done < <(comm -12 "$t/old" "$t/new")
echo "   files on both sides: $nboth; raw text differs: $nraw; code differs: $ncode"
for f in FurioLombardo/Challenge.lean FurioLombardo/Solution.lean; do
  if grep -qx "$f" "$t/old" && [ -f "$f" ]; then
    if cmp -s <(git show "$commit:$f") "$f"; then r="raw text identical"
    elif cmp -s <(git show "$commit:$f" | strip) <(strip < "$f"); then r="code identical, comments differ"
    else r="code differs"; fi
    echo "   $f: $r"
  fi
done
echo "   stripped tree sha256, $rev: $(sha256sum < "$t/list-old" | cut -c1-64)"
echo "   stripped tree sha256, working tree: $(sha256sum < "$t/list-new" | cut -c1-64)"

# 3. controls
echo "3. controls"
c=$t/ctl; mkdir "$c"
printf 'def s := "a -- b /- c"\n/- outer /- inner -/ text -/ def t := 1 -- tail\n' > "$c/a"
printf 'def s := "a -- b /- c"\n/- outer /- inner -/ other\ntext -/ def t := 1 -- other tail\n' > "$c/b"
printf 'def s := "a -- b /- d"\n/- outer /- inner -/ text -/ def t := 1 -- tail\n' > "$c/c"
printf 'def s := "a -- b /- c"\n/- outer /- inner -/ text -/ def t := 2 -- tail\n' > "$c/d"
printf '/-- doc -/\ntheorem x : 1 = 1 := rfl\n' > "$c/e"
printf '/-- a longer\ndoc -/\n\ntheorem x : 1 = 1 := rfl\n' > "$c/f"
printf "def c := '\"' -- q\ndef u := 2\n" > "$c/g"
printf "def c := '\"' -- r\ndef u := 3\n" > "$c/h"
printf 'def ab := 1\n' > "$c/i"
printf 'def a/- -/b := 1\n' > "$c/j"
f=FurioLombardo/Statement.lean
cp "$f" "$c/s0"
awk '!done && /^theorem / { sub(/^theorem /, "lemma "); done = 1 } { print }' "$f" > "$c/s1"
awk '!done && /^\/-- / { sub(/^\/-- /, "/-- An edited docstring. "); done = 1 } { print }' "$f" > "$c/s2"
for p in "a b same" "a c differs" "a d differs" "e f same" "g h differs" "i j differs" "s0 s1 differs" "s0 s2 same"; do
  set -- $p
  cmp -s "$c/$1" "$c/$2" && { echo "   FAILED: control $1 $2: the two texts are equal"; continue; }
  if cmp -s <(strip < "$c/$1") <(strip < "$c/$2"); then r=same; else r=differs; fi
  if [ "$r" = "$3" ]; then echo "   ok: control $1 $2: code $r"; else echo "   FAILED: control $1 $2: code $r, expected $3"; fi
done
echo "   (s0: $f; s1: its first theorem keyword made lemma, a code edit; s2: its first docstring edited)"
