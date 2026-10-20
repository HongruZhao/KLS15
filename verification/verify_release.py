#!/usr/bin/env python3
"""Portable source integrity/import checks. This program never invokes Lean."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import sys

LEAN_PIN = "leanprover/lean4:v4.35.0-rc3"
MATHLIB_PIN = "4beb549110aa44b87d699166cece6e3642bddf34"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
PROJECTS = {"lean_15": "KLS15", "lean_14": "KLS14"}
GENERATED_SUFFIXES = {".olean", ".ilean", ".o", ".trace"}
EXTERNAL_PREFIXES = {
    "Mathlib", "Init", "Lean", "Std", "Batteries", "Aesop", "Qq", "Cli",
    "Plausible", "ImportGraph", "ProofWidgets", "LeanSearchClient",
}


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for part in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(part)
    return h.hexdigest()


def read(path: Path):
    return json.loads(path.read_text())


def write_json(path: Path, value) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def within(path: Path, parent: Path) -> bool:
    try:
        path.resolve().relative_to(parent.resolve())
        return True
    except ValueError:
        return False


def files_under(project: Path):
    """Do not traverse a configured cache or repository metadata."""
    for directory, dirs, names in os.walk(project, followlinks=False):
        dirs[:] = [d for d in dirs if d not in {".lake", ".git", "__pycache__"}]
        for name in names:
            yield Path(directory) / name


def strip_comments(source: str) -> str:
    out = []
    i = depth = 0
    string = False
    while i < len(source):
        pair = source[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif string:
            if source[i] == "\\":
                out.extend("  ")
                i += 2
            elif source[i] == '"':
                string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif pair == "/-":
            depth = 1
            i += 2
        elif pair == "--":
            stop = source.find("\n", i)
            i = len(source) if stop < 0 else stop
        elif source[i] == '"':
            string = True
            out.append(" ")
            i += 1
        else:
            out.append(source[i])
            i += 1
    if depth:
        raise ValueError("Unterminated Lean block comment")
    return "".join(out)


def imports(path: Path) -> list[str]:
    result = []
    for line in strip_comments(path.read_text()).splitlines():
        match = re.match(r"^\s*(?:(?:public|private)\s+)?import\s+(.+?)\s*$", line)
        if match:
            result.extend(match.group(1).split())
    return result


def literal_lake_roots(project: Path) -> set[str]:
    # Lean string stripping is inappropriate for TOML: retain quoted roots.
    text = (project / "lakefile.toml").read_text()
    blocks = re.findall(r"(?m)^\s*roots\s*=\s*\[(.*?)\]", text, re.S)
    return {value for block in blocks for value in re.findall(r'"([^"\\]+)"', block)}


def load_source_spec(project: Path):
    manifest_path = project / "verification/source-manifest.json"
    manifest = read(manifest_path)
    auxiliary = {}
    if "files" in manifest:
        sources = {
            entry["path"][:-5].replace("/", "."): entry["sha256"]
            for entry in manifest["files"] if entry["path"].endswith(".lean")
        }
        schema = "portable_v3_files"
    elif "source_provenance" in manifest:
        sources = {
            module: entry["source_sha256"]
            for module, entry in manifest["source_provenance"].items()
        }
        correspondence = read(project / "verification/clean-build-final-correspondence.json")
        historical_audit = "verification/clean-build-r1/EndpointAudit.lean"
        auxiliary[historical_audit] = correspondence["endpoint_audit_source_sha256"]
        schema = "preserved_legacy_v2"
    else:
        raise ValueError("Unknown source-manifest schema")
    return manifest_path, manifest, sources, auxiliary, schema


def topo_order(graph: dict[str, list[str]]) -> list[str]:
    result = []
    state = {}
    def visit(module):
        if state.get(module) == 1:
            raise ValueError("Import cycle at " + module)
        if state.get(module) == 2:
            return
        state[module] = 1
        for dependency in graph[module]:
            visit(dependency)
        state[module] = 2
        result.append(module)
    for module in sorted(graph):
        visit(module)
    return result


def verify_project(project: Path, metadata: bool = True, source_overrides=None):
    manifest_path, manifest, sources, auxiliary, schema = load_source_spec(project)
    if source_overrides:
        sources.update(source_overrides)
    failures = []
    graph = {}
    external = set()
    listed_paths = {m.replace(".", "/") + ".lean" for m in sources}
    actual_paths = set()
    for directory, dirs, _ in os.walk(project, followlinks=False):
        for name in dirs:
            path = Path(directory) / name
            if path.is_symlink() and name not in {".lake", ".git"}:
                failures.append({"symlink_directory_payload": path.relative_to(project).as_posix()})
        dirs[:] = [d for d in dirs if d not in {".lake", ".git", "__pycache__"}]
    for path in files_under(project):
        relative = path.relative_to(project).as_posix()
        if path.is_symlink():
            failures.append({"symlink_payload": relative})
        if path.suffix == ".lean":
            actual_paths.add(relative)
        if path.suffix in GENERATED_SUFFIXES or path.name.endswith((".olean.private", ".olean.server")):
            failures.append({"internal_build_artifact": relative})
    expected_paths = listed_paths | set(auxiliary)
    if actual_paths != expected_paths:
        failures.append({"extra_lean_sources": sorted(actual_paths - expected_paths),
                         "missing_lean_sources": sorted(expected_paths - actual_paths)})
    cache = project / ".lake"
    if cache.exists() or cache.is_symlink():
        if not cache.is_symlink() or within(cache, project):
            failures.append({"internal_or_nonexternal_lake": ".lake"})
    for module, expected in sources.items():
        path = project / (module.replace(".", "/") + ".lean")
        if not path.is_file():
            continue
        if sha(path) != expected:
            failures.append({"source_hash_mismatch": module})
        imported = imports(path)
        graph[module] = [name for name in imported if name in sources]
        for name in imported:
            if name not in sources:
                external.add(name)
                if name.split(".", 1)[0] not in EXTERNAL_PREFIXES:
                    failures.append({"unresolved_local_import": name, "from": module})
    for relative, expected in auxiliary.items():
        path = project / relative
        if not path.is_file() or sha(path) != expected:
            failures.append({"historical_audit_source_mismatch": relative})
    if set(graph) == set(sources):
        try:
            topo_order(graph)
        except ValueError as error:
            failures.append({"import_graph": str(error)})
    roots = literal_lake_roots(project)
    missing_roots = set(sources) - roots
    if missing_roots:
        failures.append({"unregistered_source_roots": sorted(missing_roots)})
    if (project / "lean-toolchain").read_text().strip() != LEAN_PIN:
        failures.append({"wrong_lean_pin": True})
    package_manifest = read(project / "lake-manifest.json")
    if schema == "preserved_legacy_v2":
        historical = read(project / "verification/clean-build-r1/preflight.json")
        expected_pins = {row["name"]: row["revision"] for row in historical["dependency_pins"]}
        actual_pins = {row["name"]: row["rev"] for row in package_manifest["packages"]}
        if expected_pins != actual_pins:
            failures.append({"legacy_locked_dependency_pins_changed": True})
    mathlib = [row for row in package_manifest["packages"] if row["name"] == "mathlib"]
    if len(mathlib) != 1 or mathlib[0]["rev"] != MATHLIB_PIN:
        failures.append({"wrong_mathlib_pin": True})
    if not re.search(r'(?m)^rev\s*=\s*"' + MATHLIB_PIN + r'"\s*$',
                     (project / "lakefile.toml").read_text()):
        failures.append({"lakefile_mathlib_pin_mismatch": True})
    if "files" in manifest:
        protected_config = {"lake-manifest.json", "lakefile.toml", "lean-toolchain"}
        entries = {entry["path"]: entry for entry in manifest["files"]}
        for relative in sorted(protected_config):
            entry = entries.get(relative)
            path = project / relative
            if not entry or not path.is_file() or sha(path) != entry["sha256"]:
                failures.append({"protected_build_configuration_changed": relative})
    if metadata and "files" in manifest:
        for entry in manifest["files"]:
            relative = Path(entry["path"])
            if relative.is_absolute() or ".." in relative.parts:
                failures.append({"invalid_manifest_path": entry["path"]})
                continue
            path = project / relative
            if not path.is_file() or sha(path) != entry["sha256"]:
                failures.append({"payload_hash_mismatch": entry["path"]})
    result = {
        "status": "PASS" if not failures else "FAIL", "scope": "SOURCE_ONLY_NO_LEAN_INVOCATION",
        "project": project.name, "manifest_schema": schema,
        "manifest_sha256": sha(manifest_path), "library_source_modules": len(sources),
        "historical_auxiliary_sources": len(auxiliary), "registered_roots": len(roots),
        "external_import_names": len(external), "Lean": LEAN_PIN, "Mathlib": MATHLIB_PIN,
        "metadata_hashes_checked": metadata, "failures": failures,
    }
    return result, sources, graph, package_manifest


def wrapper_amendments(project: Path, receipt_path: Path):
    """Only four new release wrappers may change, after root's passed replay."""
    if project.name != "lean_14":
        raise ValueError("Wrapper amendments are allowed only for new lean_14 wrappers")
    receipt = read(receipt_path)
    if receipt.get("status") != "PASS":
        raise ValueError("Wrapper amendment requires a completed PASS receipt")
    projects = receipt.get("projects", [receipt])
    candidates = [row for row in projects if row.get("project") == "lean_14"]
    if len(candidates) != 1:
        raise ValueError("Receipt must identify exactly one lean_14 project")
    fresh = {row["module"]: row for row in candidates[0].get("fresh_modules", [])}
    allowed = {"KLS14", "Challenge", "AxiomAudit", "FullAudit"}
    required = allowed | {"KLSConstantImprovement.QuarticM96MixTrueCapBellman20261020TightEndpoint"}
    for module in required:
        row = fresh.get(module, {})
        if row.get("exit_code") != 0 or not row.get("standard_axioms_only"):
            raise ValueError("Missing passed fresh release replay: " + module)
        source = project / (module.replace(".", "/") + ".lean")
        if not source.is_file() or row.get("source_sha256") != sha(source):
            raise ValueError("Fresh replay source changed afterward: " + module)
    if fresh["AxiomAudit"].get("axiom_queries", 0) < 9:
        raise ValueError("Fresh public nine-query axiom audit is missing")
    _, _, original, _, _ = load_source_spec(project)
    amendments = []
    overrides = {}
    for module in allowed:
        path = project / (module + ".lean")
        current = sha(path)
        if current != original[module]:
            if fresh[module].get("source_sha256") != current:
                raise ValueError("Fresh receipt does not bind amended source: " + module)
            overrides[module] = current
            amendments.append({"path": module + ".lean", "previous_sha256": original[module],
                               "source_sha256": current, "fresh_exit_code": 0})
    return overrides, {
        "status": "PASS_ROOT_RECEIPT_GATED_NEW_WRAPPER_AMENDMENTS",
        "scope": "Only four new public wrappers are amendable; all 2951 inherited Lean sources remain hash-checked unchanged.",
        "root_receipt_sha256": sha(receipt_path), "amendments": amendments,
    }


def refresh_metadata(project: Path, wrapper_receipt: Path | None = None):
    overrides, amendment_record = ({}, None)
    if wrapper_receipt:
        overrides, amendment_record = wrapper_amendments(project, wrapper_receipt)
    result, sources, _, _ = verify_project(project, metadata=False, source_overrides=overrides)
    if result["status"] != "PASS":
        raise ValueError("Source/pin check failed; metadata refresh cannot authorize source edits: " + json.dumps(result["failures"]))
    old_path, old, _, _, schema = load_source_spec(project)
    if schema == "portable_v3_files":
        destination = old_path
        value = {k: v for k, v in old.items() if k != "files"}
        value["previous_manifest_sha256"] = sha(old_path)
    else:
        destination = project / "verification/release-v3-payload-manifest.json"
        value = {"schema": "KLS15-preserved-source-v3-metadata-overlay",
                 "preserved_source_manifest_sha256": sha(old_path),
                 "library_source_modules": len(sources)}
    value.update(metadata_refreshed_utc=datetime.now(timezone.utc).isoformat(),
                 refresh_scope=("Metadata hashes plus explicitly receipt-gated new wrapper amendments; inherited sources and pins unchanged."
                                if overrides else "Metadata hashes only; all Lean sources and pins checked unchanged."),
                 source_export_is_not_compilation=True)
    if amendment_record:
        write_json(project / "verification/release-v3-wrapper-amendments.json", amendment_record)
    value["files"] = [
        {"path": path.relative_to(project).as_posix(), "sha256": sha(path), "bytes": path.stat().st_size}
        for path in sorted(files_under(project)) if path != destination
    ]
    write_json(destination, value)
    return {"status": "PASS", "project": project.name, "manifest": destination.relative_to(project).as_posix(),
            "sha256": sha(destination), "scope": value["refresh_scope"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("operation", choices=["sources", "refresh-metadata"])
    parser.add_argument("--repository", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--project", choices=[*PROJECTS, "all"], default="all")
    parser.add_argument("--wrapper-receipt", type=Path,
                        help="Completed root PASS receipt, only for reviewed lean_14 wrapper amendments")
    args = parser.parse_args()
    names = list(PROJECTS) if args.project == "all" else [args.project]
    reports = []
    for name in names:
        project = args.repository.resolve() / name
        reports.append(refresh_metadata(project, args.wrapper_receipt) if args.operation == "refresh-metadata" else verify_project(project)[0])
    print(json.dumps({"status": "PASS" if all(r["status"] == "PASS" for r in reports) else "FAIL",
                      "reports": reports}, indent=2, ensure_ascii=False))
    return 0 if all(r["status"] == "PASS" for r in reports) else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, OSError, KeyError, json.JSONDecodeError) as error:
        print(json.dumps({"status": "FAIL", "scope": "SOURCE_ONLY_NO_LEAN_INVOCATION", "error": str(error)}, indent=2), file=sys.stderr)
        raise SystemExit(1)
