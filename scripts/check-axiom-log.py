#!/usr/bin/env python3
"""Check the output of `lake env lean scripts/MainResultsAxioms.lean` (long names make Lean wrap the lines).

Every `#print axioms` entry must list exactly propext, Classical.choice and Quot.sound, and the number of entries
must equal the expected count. Usage: scripts/check-axiom-log.py LOG [EXPECTED_COUNT]
"""
import re, sys
text = open(sys.argv[1]).read()
expected = int(sys.argv[2]) if len(sys.argv) > 2 else None
entries = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text)
std = {"propext", "Classical.choice", "Quot.sound"}
bad = [(n, a) for n, a in entries if {x.strip() for x in a.replace("\n", " ").split(",")} != std]
print(f"{len(entries)} entries, {len(bad)} with axioms other than {sorted(std)}")
for n, a in bad:
    print("BAD", n, a)
if "does not depend on any axioms" in text:
    print("note: some entries depend on no axioms")
if bad or (expected is not None and len(entries) != expected) or "error" in text.lower():
    sys.exit(1)
