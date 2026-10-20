#!/usr/bin/env python3
"""Optional isolated Lean replay. No compilation occurs without --execute."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

sys.dont_write_bytecode = True
from verify_release import (LEAN_PIN, MATHLIB_PIN, PROJECTS, STANDARD_AXIOMS,
                            read, sha, topo_order, verify_project, within, write_json)

COMMIT = "470d5ce1400764999581fd26d5d72b00d990b0f4"
LOCAL_MOUNT = Path("/Volumes/Hongru‘s Second Brain")
FLAGS = ["-j1", "-M12288", "-t0", "-DmaxSynthPendingDepth=3"]
ENTRY_MODULES = {
    "lean_15": ["ActualKLS15VerifiedEndpoints", "KLS15", "Challenge"],
    "lean_14": [
        "KLSConstantImprovement.QuarticM96MixTrueCapBellman20261020TightEndpoint",
        "KLS14", "Challenge", "AxiomAudit",
        "KLSConstantImprovement.JointRouteIncrementalAudit", "FullAudit",
    ],
}


def storage_paths(args, repository):
    mount = (args.required_mount or Path(os.environ.get("KLS_BUILD_MOUNT", str(LOCAL_MOUNT)))).expanduser()
    build = (args.build_root or Path(os.environ.get("KLS_BUILD_ROOT", str(mount / "lean/KLS14_release_v3")))).expanduser()
    if not mount.exists() or not os.path.ismount(mount):
        raise ValueError("Required external mount is absent; no directories or compilation were started")
    mount = mount.resolve()
    if mount == Path(mount.anchor):
        raise ValueError("The filesystem root is not an external build mount")
    if not within(build, mount) or within(build, repository):
        raise ValueError("Build root must resolve under the required mount and outside the repository")
    return mount, build.resolve()


def command_text(command, cwd, env):
    run = subprocess.run(command, cwd=cwd, env=env, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, text=True)
    if run.returncode:
        raise ValueError("Command failed: " + command[0] + "\n" + run.stdout[-3000:])
    return run.stdout.strip()


def package_paths(manifest, packages_root, mount, env):
    if not packages_root or not packages_root.is_dir() or not within(packages_root, mount):
        raise ValueError("Supply an existing pinned --packages-root on the required mount")
    search = []
    records = []
    for item in manifest["packages"]:
        path = packages_root / item["name"]
        if not path.is_dir():
            raise ValueError("Pinned dependency checkout is missing: " + item["name"])
        actual = command_text(["git", "-C", str(path), "rev-parse", "HEAD"], packages_root, env)
        if actual != item["rev"]:
            raise ValueError("Dependency revision mismatch: " + item["name"])
        obj = path / ".lake/build/lib/lean"
        if obj.is_dir():
            search.append(str(obj.resolve()))
        records.append({"name": item["name"], "revision": actual,
                        "cached_objects_present": obj.is_dir()})
    return search, records


def cache_rows(ledger, project_name):
    data = read(ledger)
    if "projects" in data:
        projects = [x for x in data["projects"] if x.get("project") == project_name]
        if data.get("status") != "PASS" or len(projects) != 1:
            raise ValueError("Cache receipt does not select one passed project")
        return projects[0]["source_matched_cache"]
    if data.get("project") == project_name and data.get("status") == "PASS":
        return data["source_matched_cache"]
    if data.get("status") not in {"PASS", "PASS_SOURCE_MATCHED_CACHE_BUNDLE"}:
        raise ValueError("Cache ledger must have PASS status")
    return data["rows"]


def cache_bundle(row, cache_root, mount):
    module = row["module"]
    main = cache_root / (module.replace(".", "/") + ".olean")
    expected = row.get("object_sha256") or row.get("current_object_sha256") or row.get("expected_object_sha256")
    if not main.is_file() or not within(main, mount) or not expected or sha(main) != expected:
        raise ValueError("Missing/changed source-matched cache object: " + module)
    companions = {x["suffix"]: x["sha256"] for x in row.get("companion_observed_hashes", [])}
    companions.update({x["suffix"]: x["sha256"] for x in row.get("companions", [])})
    companions.update({x["suffix"]: x["sha256"] for x in row.get("bundle", []) if x["suffix"]})
    result = [("", main, expected)]
    for suffix in [".private", ".server"]:
        choices = [Path(str(main) + suffix), Path(str(main.resolve()) + suffix)]
        present = next((p for p in choices if p.is_file()), None)
        if present:
            if suffix not in companions:
                raise ValueError("Olean-only ledger omits present " + suffix + " companion: " + module)
            if not within(present, mount) or sha(present) != companions[suffix]:
                raise ValueError("Changed cache companion: " + module + suffix)
            result.append((suffix, present, companions[suffix]))
        elif suffix in companions:
            raise ValueError("Recorded cache companion is missing: " + module + suffix)
    return result


def axiom_outputs(text):
    pattern = r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
    return [{"declaration": name, "axioms": [a.strip() for a in body.split(",") if a.strip()]}
            for name, body in re.findall(pattern, text, re.S)]


def attach_link(link, destination):
    if link.is_symlink():
        if link.resolve() != destination.resolve():
            raise ValueError("Existing link points elsewhere; preserved: " + link.name)
    elif link.exists():
        raise ValueError("Existing non-link directory is preserved: " + link.name)
    else:
        link.symlink_to(destination, target_is_directory=True)


def execute_project(args, project, build, mount):
    source_check, sources, graph, manifest = verify_project(project)
    if source_check["status"] != "PASS":
        raise ValueError("Source integrity must pass before compilation: " + json.dumps(source_check["failures"]))
    chosen = topo_order(graph) if args.mode == "all" else ENTRY_MODULES[project.name]
    if not all(module in sources for module in chosen):
        raise ValueError("Requested replay module is absent")
    if not args.lean or not args.lean.is_file():
        raise ValueError("Supply --lean pointing to an existing installed Lean executable")
    if args.mode == "entries" and (not args.cache_ledger or not args.cache_objects):
        raise ValueError("Entries replay requires a source/object/companion cache ledger and --cache-objects")
    if args.mode == "all" and args.cache_ledger:
        raise ValueError("All-source replay does not accept project cache reuse")
    base = build / project.name
    lake = base / "lake"
    objects = lake / "build/lib/lean"
    if objects.exists() and any(objects.iterdir()):
        raise ValueError("Use a new empty external project-object directory; previous evidence is preserved")
    source_lake = project / ".lake"
    if source_lake.exists() or source_lake.is_symlink():
        if not source_lake.is_symlink() or source_lake.resolve() != lake.resolve():
            raise ValueError("Existing project .lake is preserved; select its matching external build root")
    clean_env = dict(os.environ)
    clean_env.pop("LEAN_PATH", None)
    clean_env.pop("LEAN_SRC_PATH", None)
    clean_env["GIT_OPTIONAL_LOCKS"] = "0"
    version = command_text([str(args.lean), "--version"], project, clean_env)
    if "4.35.0-rc3" not in version or COMMIT[:7] not in version:
        raise ValueError("Installed compiler does not match the pinned version/commit")
    prefix = Path(command_text([str(args.lean), "--print-prefix"], project, clean_env))
    package_search, package_records = package_paths(manifest, args.packages_root, mount, clean_env)
    selected_cache = []
    if args.cache_ledger:
        if not within(args.cache_objects, mount):
            raise ValueError("Project cache objects must be on the required mount")
        for row in cache_rows(args.cache_ledger, project.name):
            module = row["module"]
            if module not in sources:
                continue
            if row["source_sha256"] != sources[module]:
                raise ValueError("Cache source mismatch: " + module)
            selected_cache.append((row, cache_bundle(row, args.cache_objects, mount)))
        covered = {row["module"] for row, _ in selected_cache} | set(chosen)
        missing = set(sources) - covered
        if missing:
            raise ValueError("Local dependencies lack source-matched cache objects: " + ", ".join(sorted(missing)))
    # Every mount, pin, source and cache gate precedes filesystem setup.
    objects.mkdir(parents=True, exist_ok=True)
    temporary = base / "tmp"
    temporary.mkdir(parents=True, exist_ok=True)
    logs = base / ("logs-" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ"))
    logs.mkdir()
    attach_link(source_lake, lake)
    attach_link(lake / "packages", args.packages_root)
    reused = []
    for row, bundle in selected_cache:
        relative = row["module"].replace(".", "/") + ".olean"
        main = objects / relative
        main.parent.mkdir(parents=True, exist_ok=True)
        file_records = []
        for suffix, path, digest in bundle:
            target = Path(str(main) + suffix)
            shutil.copyfile(path, target)
            if sha(target) != digest:
                raise ValueError("Copied cache bundle failed integrity check")
            file_records.append({"suffix": suffix, "sha256": digest, "bytes": target.stat().st_size})
        reused.append({"module": row["module"], "source_sha256": sources[row["module"]],
                       "object_sha256": bundle[0][2], "bundle": file_records})
    env = dict(clean_env, LEAN_PATH=os.pathsep.join([str(objects), *package_search, str(prefix / "lib/lean")]),
               TMPDIR=str(temporary), TMP=str(temporary), TEMP=str(temporary),
               XDG_CACHE_HOME=str(base / "cache"), MATHLIB_CACHE_DIR=str(base / "cache/mathlib"))
    receipt = {"status": "RUNNING", "project": project.name, "mode": args.mode,
               "source_check": source_check, "compiler_version": version, "compiler_sha256": sha(args.lean),
               "dependency_pins": package_records, "source_matched_cache": reused,
               "source_matched_cache_modules": len(reused), "fresh_modules": [],
               "fresh_full_source_rebuild": False, "external_dependencies_rebuilt": False,
               "root_mount_verified": True}
    receipt_path = logs / "receipt.json"
    write_json(receipt_path, receipt)
    for module in chosen:
        source = project / (module.replace(".", "/") + ".lean")
        output = objects / (module.replace(".", "/") + ".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        log = logs / (module + ".log")
        start = time.monotonic()
        with log.open("w") as stream:
            run = subprocess.run([str(args.lean), *FLAGS, "-o", str(output), str(source.relative_to(project))],
                                 cwd=project, env=env, stdout=stream, stderr=subprocess.STDOUT)
        text = log.read_text()
        reports = axiom_outputs(text)
        expected_queries = len(re.findall(r"(?m)^#print axioms\s+", source.read_text()))
        standard = all(set(row["axioms"]) <= STANDARD_AXIOMS for row in reports)
        item = {"module": module, "exit_code": run.returncode, "wall_seconds": time.monotonic() - start,
                "source_sha256": sha(source), "log_sha256": sha(log), "axiom_queries": len(reports),
                "axiom_sets": [row["axioms"] for row in reports], "standard_axioms_only": standard,
                "requested_axiom_queries": expected_queries,
                "object_sha256": sha(output) if run.returncode == 0 and output.is_file() else None,
                "object_companions": [{"suffix": suffix, "sha256": sha(Path(str(output) + suffix))}
                                      for suffix in [".private", ".server"] if Path(str(output) + suffix).is_file()]}
        receipt["fresh_modules"].append(item)
        if run.returncode or not standard or len(reports) != expected_queries or item["source_sha256"] != sources[module]:
            receipt["status"] = "FAIL"
            write_json(receipt_path, receipt)
            raise ValueError("Fresh replay failed; external log/evidence preserved for " + module)
        write_json(receipt_path, receipt)
        print(json.dumps({"project": project.name, "module": module, "exit_code": run.returncode,
                          "axiom_queries": len(reports)}), flush=True)
    unchanged = all(sha(project / (m.replace(".", "/") + ".lean")) == digest for m, digest in sources.items())
    receipt.update(status="PASS" if unchanged else "FAIL", sources_unchanged=unchanged,
                   fresh_full_source_rebuild=(args.mode == "all" and not reused and unchanged
                                              and len(receipt["fresh_modules"]) == len(sources)),
                   retained_cache_modules_after_fresh_replay=len({r["module"] for r in reused} - set(chosen)),
                   finished_utc=datetime.now(timezone.utc).isoformat())
    write_json(receipt_path, receipt)
    if not unchanged:
        raise ValueError("Sources changed during replay")
    return {"project": project.name, "status": receipt["status"], "receipt": str(receipt_path),
            "receipt_sha256": sha(receipt_path), "fresh_full_source_rebuild": receipt["fresh_full_source_rebuild"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--project", choices=[*PROJECTS, "all"], default="lean_14")
    parser.add_argument("--build-root", type=Path)
    parser.add_argument("--required-mount", type=Path)
    parser.add_argument("--packages-root", type=Path)
    parser.add_argument("--cache-ledger", type=Path)
    parser.add_argument("--cache-objects", type=Path)
    parser.add_argument("--lean", type=Path, help="Existing installed pinned Lean executable; never downloads a toolchain")
    parser.add_argument("--mode", choices=["entries", "all"], default="entries")
    parser.add_argument("--execute", action="store_true")
    args = parser.parse_args()
    repository = args.repository.resolve()
    mount, build = storage_paths(args, repository)
    names = list(PROJECTS) if args.project == "all" else [args.project]
    if not args.execute:
        checks = [verify_project(repository / name)[0] for name in names]
        if not all(row["status"] == "PASS" for row in checks):
            raise ValueError("Source integrity failed: " + json.dumps(checks))
        print(json.dumps({"status": "PASS_PLAN_ONLY_NO_COMPILER", "mode": args.mode,
                          "required_mount_present": True, "source_checks": checks,
                          "projects": names, "execute": False}, indent=2))
        return
    results = [execute_project(args, repository / name, build, mount) for name in names]
    print(json.dumps({"status": "PASS", "results": results}, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError, json.JSONDecodeError) as error:
        print(json.dumps({"status": "FAIL", "error": str(error)}, indent=2), file=sys.stderr)
        raise SystemExit(1)
