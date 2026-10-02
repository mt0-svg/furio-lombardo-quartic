#!/bin/bash
# Summary of the recorded clean build: clean_build.out and clean_build_modules.txt, both written by clean_build.sh,
# one block per run (a run starts at a line "# clean_build.sh at ..."). Per run: start time, whether it continued an
# earlier build directory (RESUME=1), its settings, the logged lake calls (batch calls and the module by module retries
# after a failed batch; clean_build.sh logs a call when it returns, so a call under way when a run was stopped is
# not in the log), the failed calls, the sum of the logged call times, the largest memory peak of a call, the
# modules that compiled (lines "Built M (t)" of lake, and the sum of their times), the last line of the run, and
# the modules of a failed batch that the run did not retry before it ended. Then the totals, the modules of a call
# that passed that have no "Built" line, with every call that names them, and each module that failed in a retry
# of one module, with the messages of that call and the run of the first later call that passed it.
# Usage: code/formal-proof/clean_build_summary.sh, from any directory; output as in clean_build_summary.out.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
out=$here/clean_build.out
mods=$here/clean_build_modules.txt

awk -v MODS="$mods" '
function flush_run() {
  if (r == 0) return
  printf "run %d: start %s UTC, %s; %s\n", r, start[r], mode[r], settings[r]
  printf "  logged lake calls %d (batch calls %d, retries of one module %d); failed calls %d (batch calls %d, retries of one module %d)\n",
    calls[r], calls[r] - rcalls[r], rcalls[r], failed[r], failed[r] - rfailed[r], rfailed[r]
  printf "  sum of logged call times %d s (%s); largest peak of a call %.1f GiB (%d calls with no peak recorded)\n",
    secs[r], hms(secs[r]), peak[r], nopeak[r]
  printf "  Built lines %d, sum of their times %d s\n", built[r], btime[r]
  printf "  last line: %s\n", (last[r] != "" ? last[r] : "none, the run ends with no result line")
  if (unretried[r] > 0) printf "  the run ended before it had retried %d modules of its last failed batch call\n", unretried[r]
}
function hms(s) { return sprintf("%d h %02d min %02d s", int(s / 3600), int((s % 3600) / 60), s % 60) }
BEGIN {
  # Built lines of clean_build_modules.txt, per run
  n = 0
  while ((getline line < MODS) > 0) {
    if (line ~ /^# clean_build\.sh at /) { n++; continue }
    if (line !~ / Built /) continue
    t = line; sub(/.*\(/, "", t); sub(/\)$/, "", t)
    if (t ~ /^[0-9.]+ms$/) { sub(/ms$/, "", t); s = t / 1000 }
    else if (t ~ /^[0-9.]+s$/) { sub(/s$/, "", t); s = t + 0 }
    else { print "clean_build_summary.sh: unread time in: " line > "/dev/stderr"; exit 1 }
    m = line; sub(/.* Built /, "", m); sub(/ \(.*$/, "", m)
    built[n]++; btime_f[n] += s; hasbuilt[m] = 1
  }
  for (i in btime_f) btime[i] = int(btime_f[i] + 0.5)
}
/^# clean_build\.sh at / {
  if (retry_left > 0) unretried[r] += retry_left
  flush_run(); r++
  start[r] = $4 " " $5; mode[r] = "clean (build directory moved aside)"; retry_left = 0; next
}
/^# settings: / { s = $0; sub(/^# settings: /, "", s); sub(/;.*/, "", s); settings[r] = s; next }
/^# RESUME=1/ { mode[r] = "RESUME=1 (continues on the build directory of the run before)"; next }
/^# package: / { pk = $0; sub(/^# package: /, "", pk); sub(/;.*/, "", pk); package = pk; next }
/^# result: / || /^# done in / { if (/^# result: /) last[r] = $0; else done[r] = $0; next }
/^error: / {
  if (errto) { e = $0; sub(/^error: [^ ]*\.lean:[0-9]+:[0-9]+: /, "error: ", e); if (!index(fmerr[errto], e)) fmerr[errto] = fmerr[errto] (fmerr[errto] == "" ? "" : "; ") e }
  next
}
/^(ok|FAILED) [0-9]+ s, peak / {
  errto = 0
  isretry = (retry_left > 0); if (isretry) retry_left--
  calls[r]++; if (isretry) rcalls[r]++
  secs[r] += $2; tsecs += $2
  if ($5 == "not") { nopeak[r]++ } else { p = $5 + 0; if (p > peak[r]) peak[r] = p }
  ms = $0; sub(/^[^:]*: /, "", ms); k = split(ms, a, " ")
  for (j = 1; j <= k; j++) seen[a[j]] = seen[a[j]] sprintf("; run %d, line %d of clean_build.out, %s %d s%s%s", r, FNR, $1, $2, (isretry ? " retry" : ""), (k > 1 ? ", a call of " k " modules" : ", a call of this module alone"))
  if ($1 == "FAILED") {
    failed[r]++
    if (isretry) { rfailed[r]++; nfm++; fm[nfm] = a[1]; fmrun[nfm] = r; errto = nfm }
    else pending = k
  } else for (j = 1; j <= k; j++) {
    okmod[a[j]] = 1
    for (i = 1; i <= nfm; i++) if (fm[i] == a[j] && !(i in fmpass)) fmpass[i] = r
  }
  next
}
/^# retry module by module/ { retry_left = pending; next }
END {
  if (retry_left > 0) unretried[r] += retry_left
  flush_run()
  for (i = 1; i <= r; i++) {
    tc += calls[i]; tf += failed[i]; trf += rfailed[i]; tb += built[i]; tbt += btime[i]
    if (peak[i] > tp) tp = peak[i]
  }
  printf "all %d runs: logged lake calls %d; failed calls %d (batch calls %d, retries of one module %d); sum of logged call times %d s (%s); largest peak %.1f GiB\n",
    r, tc, tf, tf - trf, trf, tsecs, hms(tsecs), tp
  printf "  Built lines %d, sum of their times %d s (%s)\n", tb, tbt, hms(tbt)
  printf "  package (header): %s\n", package
  nok = 0; nob = 0
  for (m in okmod) { nok++; if (!(m in hasbuilt)) { nob++; nb[nob] = m } }
  for (i = 2; i <= nob; i++) { v = nb[i]; for (j = i - 1; j >= 1 && nb[j] > v; j--) nb[j + 1] = nb[j]; nb[j + 1] = v }
  for (i = 1; i <= nob; i++) nobl = nobl " " nb[i]
  printf "  distinct modules in a call that passed: %d; of them with no Built line: %d:%s\n", nok, nob, nobl
  for (i = 1; i <= nob; i++) printf "  calls of %s (no Built line):%s\n", nb[i], substr(seen[nb[i]], 2)
  for (i = 1; i <= nfm; i++)
    printf "  failed in a retry of one module in run %d: %s; its messages: %s; first call that passed it after that: run %s\n", fmrun[i], fm[i], (fmerr[i] != "" ? fmerr[i] : "none"), (i in fmpass ? fmpass[i] : "none")
  for (i = 1; i <= r; i++) if (done[i] != "") printf "  summary line printed by run %d: %s\n", i, done[i]
}
' "$out"
