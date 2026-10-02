#!/bin/bash
# The Comparator and nanoda times of the paper, read from the two shipped job logs, which are the record:
# comparator_trial_kernel.log.gz, job "furio-lombardo-quartic kernel" (Comparator with the Lean kernel alone,
# enable_nanoda false), and comparator_trial_nanoda4.log.gz, job "furio-lombardo-quartic nanoda-4" (the export of the
# solution on the same targets as Comparator, in another order, then nanoda_bin with the configuration Comparator
# writes, 4 threads). Both jobs ran in the repository mt0-svg/nanoda-trials on GitHub hosted runners on 2026-09-30
# and checked out tag v1.1.0, which is the Lean code of this version up to comments (comment_only_build_sources.out).
# Provenance only, not in the logs: they come from run 36763054119 of that repository, downloaded on 2026-10-01 with
# trailing blanks stripped from each line, then gzipped.
# For each log this prints, verbatim with the log's timestamps: the job name, the repositories synced and the commits
# checked out, the build step that names the repository the job ran in, the nanoda install line, the steps that run
# the timed commands (their script, the configuration and machine lines they print, the export targets, the
# Comparator verdict lines), and each complete /usr/bin/time -v block, from "Command being timed" to "Exit status".
# Then one line per timed command: wall time and exit status.
# Usage: code/formal-proof/comparator_time.sh, from any directory; output as in comparator_time.out.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)

echo "# comparator_time.sh: the job logs comparator_trial_kernel.log.gz (job furio-lombardo-quartic kernel: Comparator"
echo "# with the Lean kernel alone) and comparator_trial_nanoda4.log.gz (job furio-lombardo-quartic nanoda-4: the export"
echo "# of the solution on the same targets as Comparator, then nanoda_bin, which prints no verdict line: its exit status"
echo "# is the verdict), repository mt0-svg/nanoda-trials, GitHub hosted runners, 2026-09-30. Both check out tag v1.1.0"
echo "# (d3f8953), the Lean code of this version up to comments (comment_only_build_sources.out). Provenance only, not"
echo "# in the logs: run 36763054119, logs downloaded 2026-10-01 with trailing blanks stripped."

for log in comparator_trial_kernel.log.gz comparator_trial_nanoda4.log.gz; do
  echo "== $log (sha256 $(sha256sum "$here/$log" | cut -c1-64))"
  gzip -dc "$here/$log" | awk '
    { sub(/^\xef\xbb\xbf/, ""); t = $0; sub(/^[0-9TZ:.-]+ /, "", t) }
    t ~ /^Complete job name: / || t ~ /^Syncing repository: / || t ~ /^HEAD is now at / || t ~ /^##\[start-action display=build / || t ~ /Installed package `nanoda_lib/ { print; next }
    t ~ /^##\[group\]Run lake build/ { print; sel = 0; next }
    t ~ /^##\[group\]Run / {
      sel = (t ~ /^##\[group\]Run (test "\$\(git -C \.ci\/comparator|jq |mod=|n=\$\{MODE)/); inscript = sel; pre = sel
      if (sel) print; next
    }
    t ~ /^Post job cleanup\./ { sel = 0; next }
    !sel { next }
    inscript { print; if (t ~ /^##\[endgroup\]/) inscript = 0; next }
    t ~ /^\tCommand being timed:/ { intime = 1; pre = 0 }
    intime { print; if (t ~ /^\tExit status:/) intime = 0; next }
    t ~ /^(Running as unit|Building FurioLombardo|Exporting )/ { pre = 0 }
    pre { print; next }
    t ~ /^(Building FurioLombardo\.(Challenge|Solution)$|Build completed|Exporting |Running .*kernel|.*kernel (accepts|rejects)|Your solution|uncaught|error)/ || t ~ /^-rw/ { print }
  '
done

echo "== summary: wall time and exit status of each timed command"
for log in comparator_trial_kernel.log.gz comparator_trial_nanoda4.log.gz; do
  gzip -dc "$here/$log" | awk -v lf="$log" '
    { t = $0; sub(/^[^ ]+ /, "", t) }
    t ~ /^\tCommand being timed:/ { c = (t ~ /comparator trial\.json/ ? "Comparator (Lean kernel alone)" : t ~ /lean4export/ ? "lean4export (export of the solution)" : t ~ /nanoda_bin/ ? "nanoda_bin (4 threads)" : "other command") }
    t ~ /^\tElapsed \(wall clock\)/ { w = t; sub(/.*: /, "", w) }
    t ~ /^\tExit status:/ { e = t; sub(/.*: /, "", e); printf "%s: %s, wall %s, exit status %s\n", lf, c, w, e }
  '
done
