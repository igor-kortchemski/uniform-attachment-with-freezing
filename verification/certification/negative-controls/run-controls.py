#!/usr/bin/env python3
"""Negative controls for the LOCAL comparison diagnostic (not the official Comparator).

Creates deliberately wrong copies `Challenge/Mut*.lean` of `Challenge/Heights.lean`, builds each, runs
`scripts/local-comparator-diagnostic.sh` against the unchanged `Solution.Heights`, records whether the
diagnostic rejects it, and deletes the mutants and their build products. Expected: every control is rejected.
The Challenge/Solution/config files of the real interface are never modified.

Usage (from the project root, after `lake build Challenge.Heights Solution.Heights`):
    python3 verification/certification/negative-controls/run-controls.py OUTDIR
"""
import json, os, re, shutil, subprocess, sys

root = os.getcwd()
out = os.path.abspath(sys.argv[1]); os.makedirs(out, exist_ok=True)
src = open("Challenge/Heights.lean").read()
cfg = json.load(open("comparator/heights.json"))

def sub(old, new, text=src):
    assert text.count(old) == 1, (old, text.count(old))
    return text.replace(old, new)

mutants = {
    # a reachable definition inside the forward process: uniform choice over all vertices instead of active ones
    "MutC": ("transitionLaw samples any vertex, not only active ones",
             sub("(Measure.uniformOfFinset s.active).map (fun v => step s t sign v)",
                 "(Measure.uniformOfFinset s.vertices).map (fun v => step s t sign v)")),
    # a reachable definition used by one statement: the second sampled vertex ranges over active vertices only
    "MutD": ("forwardPairKernel: second vertex uniform among active vertices",
             sub("(Measure.uniformOfFinset s.vertices).map fun v =>", "(Measure.uniformOfFinset s.active).map fun v =>")),
    # the roles of +1 and -1 swapped in the transition
    "MutE": ("step: attachment and freezing swapped",
             sub("if v ∈ s.active then if sign then attach s t v else freeze s t v else s",
                 "if v ∈ s.active then if sign then freeze s t v else attach s t v else s")),
}
results = []
def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)

for name, (what, text) in mutants.items():
    path = f"Challenge/{name}.lean"
    open(path, "w").write(text)
    try:
        b = run(["lake", "build", f"Challenge.{name}"])
        if b.returncode != 0:
            results.append((name, what, "BUILD FAILED", b.stderr[-300:])); continue
        c = dict(cfg, challenge_module=f"Challenge.{name}")
        cpath = os.path.join(out, f"{name}.json"); json.dump(c, open(cpath, "w"))
        d = os.path.join(out, name)
        r = run(["sh", "scripts/local-comparator-diagnostic.sh", cpath, d])
        log = open(os.path.join(d, "compare.log")).read() if os.path.exists(os.path.join(d, "compare.log")) else r.stdout + r.stderr
        verdict = "REJECTED" if "COMPARE FAILED" in log or "FAILED" in log else ("ACCEPTED (BAD)" if "match" in log else "UNKNOWN")
        results.append((name, what, verdict, log.strip().splitlines()[-1] if log.strip() else ""))
        for f in ("challenge.ndjson", "solution.ndjson", "diag.c", "localdiag"):
            p = os.path.join(d, f)
            if os.path.exists(p): os.remove(p)
    finally:
        for ext in ("lean",):
            if os.path.exists(path): os.remove(path)
        for pat in (f".lake/build/lib/lean/Challenge/{name}", f".lake/build/ir/Challenge/{name}"):
            for suffix in ("", ".olean", ".ilean", ".olean.hash", ".trace", ".ir", ".c", ".c.hash", ".olean.private",
                           ".olean.server", ".ir.hash", ".ir.sig", ".ilean.hash"):
                p = pat + suffix
                if os.path.exists(p): os.remove(p)
with open(os.path.join(out, "controls.md"), "w") as f:
    f.write("| Mutant | Change | Verdict | Last line of the diagnostic |\n| --- | --- | --- | --- |\n")
    for r in results:
        f.write("| {} | {} | {} | `{}` |\n".format(*r))
print(open(os.path.join(out, "controls.md")).read())
