#!/bin/sh
# extract_lean_data.sh: copy the Lean data defining K21 (fL), its integral basis zk (Dz, zkNum) and the Prym sextics
# (FnData) into GP syntax, so that schaefer_global_check.gp works on the objects the Lean statements are about.
# Run from code/second-implementations/schaefer: sh extract_lean_data.sh > lean_data.gp
L=../../../FurioLombardo
ext() { # file, Lean name, GP name: the term after "def <name> ... :=" up to the next blank line, doc comment or def
  awk -v n="$2" -v g="$3" '
    on && ($0 ~ /^\/--/ || $0 ~ /^def / || $0 ~ /^$/) { on = 0; print ";" }
    $0 ~ "^def " n " " { on = 1; sub(/^.*:=/, ""); printf "%s = ", g }
    on { printf "%s", $0 }
  ' "$1"
}
ext $L/M1/Basic.lean fL LfL
ext $L/M1/DataField.lean Dz LDz
ext $L/M1/DataField.lean zkNum LzkNum
ext $L/Discharge/M3a/DataBruin.lean FnData LFnData
