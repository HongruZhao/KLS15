#!/usr/bin/env python3
"""Check the portable source manifest without invoking Lean or writing caches."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent
manifest = json.loads((ROOT / "verification/source-manifest.json").read_text())
failures = []
for entry in manifest["files"]:
    relative = Path(entry["path"])
    if relative.is_absolute() or ".." in relative.parts:
        failures.append({"invalid_path": entry["path"]})
        continue
    path = ROOT / relative
    if not path.is_file() or path.is_symlink():
        failures.append({"missing_or_symlink": entry["path"]})
    elif hashlib.sha256(path.read_bytes()).hexdigest() != entry["sha256"]:
        failures.append({"hash_mismatch": entry["path"]})
source_paths = {x["path"] for x in manifest["files"] if x["path"].endswith(".lean")}
actual_sources = {
    p.relative_to(ROOT).as_posix() for p in ROOT.rglob("*.lean")
    if ".lake" not in p.relative_to(ROOT).parts
}
if actual_sources != source_paths:
    failures.append({"unlisted_sources": sorted(actual_sources - source_paths),
                     "missing_sources": sorted(source_paths - actual_sources)})
closure = json.loads((ROOT / "verification/import-closure.json").read_text())
for module, dependencies in closure["local_imports"].items():
    for dependency in [module, *dependencies]:
        if dependency.replace(".", "/") + ".lean" not in source_paths:
            failures.append({"unresolved_local_import": dependency, "from": module})
result = {"status": "PASS" if not failures else "FAIL",
          "source_files": len(source_paths), "manifest_files": len(manifest["files"]),
          "scope": "Source integrity and local import closure only; no Lean compilation.",
          "failures": failures}
print(json.dumps(result, indent=2))
raise SystemExit(bool(failures))
