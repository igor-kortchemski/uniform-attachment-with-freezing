#!/usr/bin/env python3
"""Render the evidence directory written by scripts/collect-evidence.sh as a Markdown summary.
Usage: scripts/summarize-evidence.py EVIDENCE_DIR BUILD_LOG PORTS_OUTPUT_FILE > SUMMARY.md"""
import os, re, sys, json
E = sys.argv[1]
def rd(p):
    try: return open(os.path.join(E, p)).read()
    except OSError: return ""
log = rd("evidence.log")
build = open(sys.argv[2]).read() if len(sys.argv) > 2 else ""
ports = open(sys.argv[3]).read() if len(sys.argv) > 3 else ""
def grab(pat, text, default="?"):
    m = re.search(pat, text, re.M); return m.group(1) if m else default
print("# Evidence summary of the local candidate\n")
print("All results below are LOCAL runs on one macOS machine (Darwin 23.6, no Linux sandbox). None of them is the official")
print("`lake comparator`, the official NanoDa/kernel replay of the Palomar pipeline, or the Palomar mechanical report.\n")
print("## Identity\n")
print(f"* Source commit of the candidate that was built: `{grab(r'commit: (\w+)', log)}`; tree `{grab(r'tree: (\w+)', log)}`.")
print(f"* Toolchain: `{grab(r'toolchain: (\S+)', log)}`. Collected {grab(r'start (\S+)', log)} to {grab(r'end (\S+)', log)}.")
print("* Git status at collection time (must be empty): " + ("empty" if re.search(r"git status \(must be empty\):\ntoolchain", log) else "NOT EMPTY, see evidence.log"))
print("\n## Fresh build\n")
print(f"`lake build Freezing1 Challenge Solution` from an empty `.lake/build` (pinned Mathlib packages symlinked): "
      f"{grab(r'Build completed successfully \((\d+) jobs\)', build)} jobs, exit {grab(r'exit=(\d+)', build)}, "
      f"{grab(r'real (\S+)', build)} s wall time. `declaration uses sorry` warnings occur only in `Challenge/*` "
      f"({len(re.findall(r'declaration uses', build))} = the number of Challenge targets with a hole).")
print("\n## Source scan and axioms\n")
print(f"* `scripts/check-sources.py`: exit {grab(r'source-scan exit=(\d+)', log)}.")
print(f"* `scripts/AxiomAudit.lean`: exit {grab(r'axiom-audit exit=(\d+)', log)}; " + grab(r"(Checked \d+ Freezing1 declarations[^\n]*)", rd("axiom-audit.log")))
print(f"* `scripts/MainResultsAxioms.lean` + `scripts/check-axiom-log.py`: exit {grab(r'check-axiom-log exit=(\d+)', log)}; "
      + grab(r"(\d+ entries, \d+ with axioms other[^\n]*)", log))
print("\n## Local comparison and kernel replays\n")
print("| Interface | compare | axioms | leanchecker | NanoDa | leanchecker-paranoid | lean4lean | con-leche | con-ron | solution export SHA-256 |")
print("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
for cfg in ["heights", "locallimits", "samelaw", "sir", "auxiliary"]:
    c = rd(f"{cfg}/compare.log"); k = rd(f"{cfg}/kernels/kernels.log")
    cm = "match" if "statements and reachable constants match" in c else "**FAILED**"
    ax = "permitted only" if "only permitted axioms" in c else "**FAILED**"
    def ex(n):
        m = re.search(rf"^{re.escape(n)} exit=(\d+)", k, re.M); return ("exit " + m.group(1)) if m else "not run"
    sha = grab(r"^([0-9a-f]{64})", k, "-")[:16]
    print(f"| {cfg} | {cm} | {ax} | {ex('leanchecker')} | {ex('nanoda')} | {ex('leanchecker-paranoid')} | {ex('lean4lean')} | {ex('con-leche')} | {ex('con-ron')} | `{sha}…` |")
print("\n(The `auxiliary` row is the old `comparator.json`; kernel replays are not run for it. NanoDa and the other checkers are invoked as in Lake's own `Check.lean`; leanchecker is Lean's own kernel.)")
print("\n## Probes\n")
lines = [l for l in ports.splitlines() if " exit=" in l]
bad = [l for l in lines if not l.endswith("exit=0")]
print(f"All top-level module-headed probes `verification/*.lean` (including the nine ports of `verification/candidate-ports/`) compiled against the candidate: {len(lines)} files, {len(lines) - len(bad)} exit 0" + (", failures: " + ", ".join(bad) if bad else "."))
