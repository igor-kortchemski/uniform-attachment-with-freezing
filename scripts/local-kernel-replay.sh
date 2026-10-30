#!/bin/sh
# LOCAL KERNEL REPLAY ONLY. This is not `lake comparator` and not the Palomar pipeline: it runs
# outside the Linux sandbox. It replays the Solution export written by
# `scripts/local-comparator-diagnostic.sh` with the checkers bundled in the Lean toolchain, invoking
# each exactly as Lake's own `Check.lean` does (nanoda gets a JSON config file with the permitted
# axioms; the others get the export path).
#
# Mandatory in the official protocol: Lean's kernel and NanoDa. Advisory here: lean4lean, con-leche,
# con-ron and the paranoid Lean checker.
# Usage: scripts/local-kernel-replay.sh CONFIG.json SOLUTION.ndjson OUTDIR
set -u
CFG="$1"; SOL="$2"; OUT="$3"; mkdir -p "$OUT"
cd "$(dirname "$0")/.." || exit 2
TC="$(lake env printenv LEAN_SYSROOT 2>/dev/null)"
[ -z "$TC" ] && TC="$(dirname "$(dirname "$(lake env which lean)")")"
BIN="$TC/bin"
AX="$(python3 - "$CFG" <<'PY'
import json,sys
print(json.dumps(json.load(open(sys.argv[1]))["permitted_axioms"]))
PY
)"
NCFG="$OUT/nanoda-config.json"
printf '{"use_stdin":false,"export_file_path":"%s","permitted_axioms":%s,"unpermitted_axiom_hard_error":false,"num_threads":2,"nat_extension":true,"string_extension":true}\n' "$SOL" "$AX" > "$NCFG"
date -u +"start %Y-%m-%dT%H:%M:%SZ" | tee "$OUT/kernels.log"
shasum -a 256 "$SOL" | tee -a "$OUT/kernels.log"
run() { # name, then command
  name="$1"; shift
  echo "== $name: $*" | tee -a "$OUT/kernels.log"
  ( time "$@" ) > "$OUT/$name.out" 2>&1
  code=$?
  tail -n 4 "$OUT/$name.out" | tee -a "$OUT/kernels.log"
  echo "$name exit=$code" | tee -a "$OUT/kernels.log"
}
run leanchecker "$BIN/leanchecker" --silent --from-export "$SOL"
run nanoda "$BIN/nanoda_bin" "$NCFG"
run leanchecker-paranoid "$BIN/leanchecker-paranoid" --silent --from-export "$SOL"
run lean4lean "$BIN/lean4lean" --import "$SOL"
run con-leche "$BIN/con-leche" "$SOL"
run con-ron "$BIN/con-ron" "$SOL"
echo "(local replay outside the sandbox; official mandatory checkers: Lean and NanoDa)" | tee -a "$OUT/kernels.log"
