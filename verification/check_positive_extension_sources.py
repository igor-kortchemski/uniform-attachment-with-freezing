#!/usr/bin/env python3
"""Kernel-check the A63 sources and expanded probe without writing artifacts.

The root controls all Lake artifact builds. This source-only check is useful
when those dependency artifacts are pending; it never replaces release builds.
"""

from pathlib import Path
import hashlib
import json
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
NAMES = [
    "ForwardPositiveExtension",
    "SignedUrnPositiveExtension",
    "SignedUrnPositiveExtensionBounds",
    "SignedUrnPositiveExtensionPath",
    "SignedUrnPositiveExtensionMaximal",
]
FILES = [Path("Freezing1") / (name + ".lean") for name in NAMES]
FILES.append(Path("verification/PositiveExtensionStatements.lean"))
LOCAL_IMPORTS = {"Freezing1." + name for name in NAMES}
imports = []
bodies = []
manifest = {}
for relative in FILES:
    source = (ROOT / relative).read_text()
    manifest[str(relative)] = hashlib.sha256(source.encode()).hexdigest()
    body = []
    for line in source.splitlines():
        if line == "module":
            continue
        if line.startswith("public import ") or line.startswith("import "):
            module = line.split()[-1]
            canonical = "public import " + module
            if module not in LOCAL_IMPORTS and canonical not in imports:
                imports.append(canonical)
        else:
            body.append(line)
    bodies.append("\n".join(body))

(ROOT / "verification/positive-extension-source-snapshot.json").write_text(
    json.dumps(manifest, indent=2) + "\n"
)
combined = "module\n\n" + "\n".join(imports) + "\n\n" + "\n".join(bodies)
with tempfile.TemporaryDirectory(prefix="freezing1-positive-extension-") as folder:
    path = Path(folder) / "PositiveExtensionSourceStatements.lean"
    path.write_text(combined)
    log = ROOT / "verification/positive-extension-source-statements.log"
    with log.open("w") as output:
        result = subprocess.run(
            ["lake", "env", "lean", "-DautoImplicit=false", str(path)],
            cwd=ROOT, stdout=output, stderr=subprocess.STDOUT, check=False,
        )
print(f"A63 source-only kernel check: exit {result.returncode}; {log}")
raise SystemExit(result.returncode)
