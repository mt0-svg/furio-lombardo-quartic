#!/bin/bash
# Convert the Lean data lists used by the prime count certificates into a gp include file
# (sunit_leandata.gp): M1's gensL, unitsL, M3b's epsL, xCL, yCL, alL, beL, nxL, alnL, benL, nnL.
set -eu
cd "$(dirname "$0")/../../FurioLombardo"
conv() { # file name
  awk -v n="$2" '
    $0 ~ ("^def " n " ") {on=1; sub(/^def [^=]*:= */, ""); }
    on { buf = buf $0; if (buf ~ /\][[:space:]]*$/ && depth(buf) == 0) { print n " = " buf ";"; on=0; buf="" } }
    function depth(s,   i, c, d) { d = 0; for (i = 1; i <= length(s); i++) { c = substr(s, i, 1); if (c == "[") d++; if (c == "]") d-- } return d }
  ' "$1"
}
{
  conv M1/DataGens.lean gensL
  conv M1/DataGens.lean unitsL
  conv Discharge/M3b/K21Defs.lean epsL
  conv Discharge/M3b/DataK21.lean xCL
  conv Discharge/M3b/DataK21.lean yCL
  for n in alL beL nxL alnL benL nnL eaL ebL mL; do conv Discharge/M3b/DataL.lean $n; done
} > ../../code/selmer-global-bound/sunit_leandata.gp
