#!/usr/bin/env python3
"""Source scan of the maintained Lean files (a text scan, not a proof check).

Checks every `.lean` file outside `.lake`: first line is `module`; at most 1000 lines; no `native_decide`,
`bv_decide`, `axiom`/`opaque`/`unsafe`/`implemented_by`/`extern` declaration, no bare `import Mathlib`;
`sorry` only in `Challenge/` (deliberate target holes) and never elsewhere; Challenge files at most 100 KiB
and importing only Mathlib/Lean-core modules (never `Freezing1`). Exit status 1 on any violation.
Usage: scripts/check-sources.py [ROOT]
"""
import os, re, sys

root = os.path.abspath(sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(__file__), ".."))
bad = []
count = 0
forbidden = re.compile(r"\b(native_decide|bv_decide|implemented_by|extern|unsafe)\b|^\s*(axiom|opaque)\s")
for d, dirs, files in os.walk(root):
    dirs[:] = [x for x in dirs if x not in (".lake", ".git", ".scratch")]
    for f in files:
        if not f.endswith(".lean"):
            continue
        p = os.path.join(d, f)
        rel = os.path.relpath(p, root)
        count += 1
        text = open(p, encoding="utf-8").read()
        lines = text.split("\n")
        if lines[0].strip() != "module":
            bad.append(f"{rel}: first line is not `module`")
        if len(lines) - (1 if lines[-1] == "" else 0) > 1000:
            bad.append(f"{rel}: more than 1000 lines")
        code = re.sub(r"/-.*?-/", "", text, flags=re.S)
        code = re.sub(r"--[^\n]*", "", code)
        for i, line in enumerate(code.split("\n"), 1):
            if forbidden.search(line):
                bad.append(f"{rel}: forbidden construct: {line.strip()[:80]}")
            if re.match(r"\s*(public\s+)?(meta\s+)?import\s+Mathlib\s*$", line):
                bad.append(f"{rel}: bare `import Mathlib`")
        in_challenge = rel.startswith("Challenge" + os.sep) or rel == "Challenge.lean"
        n_sorry = len(re.findall(r"\bsorry\b", code))
        if n_sorry and not in_challenge:
            bad.append(f"{rel}: `sorry` outside Challenge ({n_sorry})")
        if in_challenge:
            if len(text.encode()) > 100 * 1024:
                bad.append(f"{rel}: larger than 100 KiB")
            for line in text.split("\n"):
                m = re.match(r"\s*(?:public\s+)?(?:meta\s+)?import\s+(\S+)", line)
                if m and not re.match(r"(Mathlib|Lean|Init|Std|Batteries)\b", m.group(1)):
                    bad.append(f"{rel}: Challenge imports {m.group(1)}")
print(f"scanned {count} Lean files under {root}")
for b in bad:
    print("VIOLATION", b)
sys.exit(1 if bad else 0)
