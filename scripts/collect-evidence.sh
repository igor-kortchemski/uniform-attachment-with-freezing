#!/bin/sh
# Collect the local evidence for a candidate checkout, in order, into OUT (outside the checkout).
# Everything here is a LOCAL check outside the Linux sandbox; none of it is the official Comparator or
# the Palomar mechanical report. Run from a clean checkout after `lake build Freezing1 Challenge Solution`.
# Usage: scripts/collect-evidence.sh OUT [ROOT]   (ROOT defaults to the parent of this script)
set -u
OUT="$1"; mkdir -p "$OUT"
cd "${2:-$(dirname "$0")/..}" || exit 2
LOG="$OUT/evidence.log"
{
  date -u +"start %Y-%m-%dT%H:%M:%SZ"
  echo "commit: $(git rev-parse HEAD 2>/dev/null)  tree: $(git rev-parse 'HEAD^{tree}' 2>/dev/null)"
  echo "git status (must be empty):"; git status --porcelain
  echo "toolchain: $(cat lean-toolchain)"; lake env lean --version; lake --version
  shasum -a 256 lean-toolchain lake-manifest.json lakefile.toml
  uname -a
} > "$LOG" 2>&1
echo "== lake build (must report success; artifacts already built)" >> "$LOG"
( time lake build Freezing1 Challenge Solution ) >> "$LOG" 2>&1; echo "build exit=$?" >> "$LOG"
echo "== source scan" >> "$LOG"
python3 scripts/check-sources.py >> "$LOG" 2>&1; echo "source-scan exit=$?" >> "$LOG"
echo "== axiom audit of the Freezing1 namespace" >> "$LOG"
( time lake env lean scripts/AxiomAudit.lean ) > "$OUT/axiom-audit.log" 2>&1; echo "axiom-audit exit=$?" >> "$LOG"
echo "== axioms of the exported main results" >> "$LOG"
lake env lean scripts/MainResultsAxioms.lean > "$OUT/main-results-axioms.log" 2>&1; echo "main-results-axioms exit=$?" >> "$LOG"
python3 scripts/check-axiom-log.py "$OUT/main-results-axioms.log" 26 >> "$LOG" 2>&1; echo "check-axiom-log exit=$?" >> "$LOG"
for cfg in heights locallimits samelaw sir; do
  echo "== $cfg: local comparison" >> "$LOG"
  scripts/local-comparator-diagnostic.sh "comparator/$cfg.json" "$OUT/$cfg" > "$OUT/$cfg.diag.log" 2>&1
  tail -n 4 "$OUT/$cfg/compare.log" >> "$LOG" 2>&1
  echo "== $cfg: kernel replays" >> "$LOG"
  scripts/local-kernel-replay.sh "comparator/$cfg.json" "$OUT/$cfg/solution.ndjson" "$OUT/$cfg/kernels" > "$OUT/$cfg.kernels.log" 2>&1
  grep -E "exit=" "$OUT/$cfg/kernels/kernels.log" >> "$LOG" 2>&1
done
echo "== auxiliary (comparator.json): local comparison" >> "$LOG"
scripts/local-comparator-diagnostic.sh comparator.json "$OUT/auxiliary" > "$OUT/auxiliary.diag.log" 2>&1
tail -n 4 "$OUT/auxiliary/compare.log" >> "$LOG" 2>&1
date -u +"end %Y-%m-%dT%H:%M:%SZ" >> "$LOG"
