#!/usr/bin/env python3
"""Export an isolated local candidate tree from the development tree (read-only on the source).

Usage: scripts/export_candidate.py DEST
Copies an explicit allowlist: the Lake project files, the whole `Freezing1` library, the Challenge and
Solution modules named by `comparator.json` and `comparator/*.json`, the comparator configurations,
scripts, workflows, documentation and the non-Lean verification evidence. Lean files under
`verification/` are copied only if they start with `module`; the nine probes without a module header
are replaced by the module ports in `verification/candidate-ports/`. The manuscript source file, the
`.lake` directory, `.git`, scratch files and worker drafts are not copied. Writes `MANIFEST.sha256`
(SHA-256 of every copied file). Nothing is removed or modified in the development tree.
"""
import json, os, shutil, sys, glob

src = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
dest = os.path.abspath(sys.argv[1])
if os.path.exists(dest):
    sys.exit(f"refusing to overwrite existing {dest}")

def copy(rel):
    s = os.path.join(src, rel)
    d = os.path.join(dest, rel)
    os.makedirs(os.path.dirname(d), exist_ok=True)
    if os.path.isdir(s):
        shutil.copytree(s, d, ignore=shutil.ignore_patterns(".DS_Store", "*.bak", "__pycache__"))
    else:
        shutil.copy2(s, d)

files = ["lakefile.toml", "lean-toolchain", "lake-manifest.json", "LICENSE", "NOTICE", "CITATION.cff",
         "README.md", "FORMALIZATION_REPORT.md", "MANUSCRIPT_RECOMMENDATIONS.md",
         "formalization.yaml", "comparator.json", "Freezing1.lean", "Challenge.lean", "Solution.lean",
         ".gitignore"]
for f in files:
    copy(f)
for d in ["Freezing1", "comparator", "scripts", ".github"]:
    copy(d)

modules = set()
for cfg in ["comparator.json"] + sorted(glob.glob(os.path.join(src, "comparator", "*.json"))):
    c = json.load(open(cfg if os.path.isabs(cfg) else os.path.join(src, cfg)))
    modules.add(c["challenge_module"]); modules.add(c["solution_module"])
for m in sorted(modules):
    rel = m.replace(".", "/") + ".lean"
    if os.path.exists(os.path.join(src, rel)):
        copy(rel)

# verification evidence: non-Lean files, module-headed Lean files, and the module ports
vsrc = os.path.join(src, "verification")
for root, dirs, fs in os.walk(vsrc):
    dirs[:] = [d for d in dirs if d != "candidate-ports"]
    for f in fs:
        p = os.path.join(root, f)
        rel = os.path.relpath(p, src)
        if f.endswith(".lean"):
            first = open(p).readline().strip()
            if not first.startswith("module"):
                continue
        if f in (".DS_Store",) or f.endswith(".bak") or f.endswith(".ndjson"):
            continue
        # logs of earlier local diagnostics are stale for the candidate; fresh ones are added by an evidence commit
        if rel.startswith(os.path.join("verification", "certification") + os.sep) and \
                f in ("compare.log", "run.log", "leanchecker.log", "compare-attempt1-failed.log"):
            continue
        copy(rel)
for p in sorted(glob.glob(os.path.join(vsrc, "candidate-ports", "*.lean"))):
    shutil.copy2(p, os.path.join(dest, "verification", os.path.basename(p)))
import hashlib
lines = []
for root_, dirs, fs in os.walk(dest):
    dirs[:] = sorted(d for d in dirs if d not in (".lake", ".git"))
    for f in sorted(fs):
        if f == "MANIFEST.sha256":
            continue
        p = os.path.join(root_, f)
        with open(p, "rb") as fh:
            lines.append(f"{hashlib.sha256(fh.read()).hexdigest()}  {os.path.relpath(p, dest)}")
with open(os.path.join(dest, "MANIFEST.sha256"), "w") as fh:
    fh.write("\n".join(sorted(lines, key=lambda l: l.split("  ", 1)[1])) + "\n")
print("exported to", dest, f"({len(lines)} files, MANIFEST.sha256 written)")
