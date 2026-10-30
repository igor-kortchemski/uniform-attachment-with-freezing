#!/bin/sh
# LOCAL DIAGNOSTIC ONLY. This is not `lake comparator` and not the Palomar pipeline:
# it runs outside the Linux sandbox. It exports the Challenge and Solution modules of a
# Comparator configuration with the toolchain's `leanexport`, applies Lake's own comparison
# functions, and replays the Solution export with the toolchain-bundled checkers.
# Usage: scripts/local-comparator-diagnostic.sh CONFIG.json OUTDIR
set -u
CFG="$1"; OUT="$2"; mkdir -p "$OUT"
cd "$(dirname "$0")/.." || exit 2
TC="$(lake env printenv LEAN_SYSROOT 2>/dev/null)"
[ -z "$TC" ] && TC="$(dirname "$(dirname "$(lake env which lean)")")"
BIN="$TC/bin"
eval "$(python3 - "$CFG" <<'PY'
import json,sys
c=json.load(open(sys.argv[1]))
print("CH=%s"%c["challenge_module"]); print("SO=%s"%c["solution_module"])
prim="Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String Char optParam autoParam semiOutParam outParam Quot Quot.mk Quot.lift Quot.ind".split()
names=prim+c["theorem_names"]+c.get("permitted_axioms",[])+c.get("definition_names",[])
print("TARGETS='%s'"%" ".join(names))
PY
)"
echo "challenge=$CH solution=$SO"
date -u +"start %Y-%m-%dT%H:%M:%SZ" | tee "$OUT/run.log"
( time lake env "$BIN/leanexport" "$CH" -- $TARGETS > "$OUT/challenge.ndjson" ) 2>> "$OUT/run.log"; echo "export challenge exit=$?" | tee -a "$OUT/run.log"
( time lake env "$BIN/leanexport" "$SO" -- $TARGETS > "$OUT/solution.ndjson" ) 2>> "$OUT/run.log"; echo "export solution exit=$?" | tee -a "$OUT/run.log"
ls -l "$OUT"/*.ndjson | tee -a "$OUT/run.log"
lake env lean -c "$OUT/diag.c" scripts/LocalComparatorDiagnostic.lean || exit 2
"$BIN/leanc" "$OUT/diag.c" -o "$OUT/localdiag" -L"$TC/lib/lean" -lLeanExport -lLake -lLean -lStd -lInit -lleancpp -lleanrt || exit 2
"$OUT/localdiag" "$CFG" "$OUT/challenge.ndjson" "$OUT/solution.ndjson" 2>&1 | tee "$OUT/compare.log"
( time "$BIN/leanchecker" --silent --from-export "$OUT/solution.ndjson" ) > "$OUT/leanchecker.log" 2>&1; echo "leanchecker exit=$?" | tee -a "$OUT/run.log"
echo "(nanoda and other bundled checkers are run separately: see the certification notes)" | tee -a "$OUT/run.log"
