#!/usr/bin/env python3
"""Validate wrapped Lean axiom output, distinct names and the permitted set.

Usage: check-axiom-log.py LOG [EXPECTED_COUNT] [--declarations SOURCE.lean]
With --declarations, require exactly the names queried by #print axioms in
that source. Empty/subset axiom closures are valid; extra axioms never are.
"""
import argparse
from collections import Counter
from pathlib import Path
import re
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path)
    parser.add_argument("expected_count", nargs="?", type=int)
    parser.add_argument("--declarations", type=Path)
    args = parser.parse_args()
    text = args.log.read_text()
    entries = [(n, {a.strip() for a in axioms.split(",") if a.strip()}) for n, axioms in
               re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)]
    entries += [(n, set()) for n in re.findall(r"'([^']+)' does not depend on any axioms", text)]
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    bad = [(n, sorted(axioms - allowed)) for n, axioms in entries if not axioms <= allowed]
    duplicates = sorted(n for n, count in Counter(n for n, _ in entries).items() if count > 1)
    errors = []
    if not entries:
        errors.append("no complete axiom reports found")
    if re.search(r"\berror(?:\([^)]*\))?:", text):
        errors.append("Lean error in log")
    if args.expected_count is not None and len(entries) != args.expected_count:
        errors.append(f"expected {args.expected_count} reports, got {len(entries)}")
    if args.declarations:
        expected = re.findall(r"^\s*#print\s+axioms\s+(\S+)", args.declarations.read_text(), re.M)
        actual = {n for n, _ in entries}
        if len(set(expected)) != len(expected):
            errors.append("duplicate #print axioms query in source")
        if actual != set(expected):
            errors.append(f"missing names: {sorted(set(expected) - actual)}; unexpected names: {sorted(actual - set(expected))}")
    print(f"{len(entries)} entries, {len(bad)} with forbidden axioms, {len(duplicates)} duplicate names")
    for item in bad:
        print("FORBIDDEN", item)
    for error in [*(f"duplicate report: {name}" for name in duplicates), *errors]:
        print("ERROR", error)
    return 1 if bad or duplicates or errors else 0


if __name__ == "__main__":
    sys.exit(main())
