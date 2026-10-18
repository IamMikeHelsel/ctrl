#!/usr/bin/env python3
"""Copy frozen project sources, rebuild them, and retain independent evidence.

Run only after the project sources and generated audit inventory are frozen:
  python3 publication/replay_source_snapshot.py --prefix travel-fresh-replay

This replays check.sh, not generator tests or numerical design. It reuses an
existing pinned toolchain and a disclosed isolated dependency cache. No original
project .lake directory or project build product is copied. Outputs are never
overwritten. The scratch project is retained for inspection.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time


PUBLICATION = Path(__file__).resolve().parent
WORKSPACE = PUBLICATION.parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
SKIP_DIRS = {".lake", ".git", "__pycache__", ".pytest_cache"}
BUILD_SUFFIXES = {".olean", ".ilean", ".ir", ".trace", ".pyc", ".o"}


def utc():
    return datetime.now(timezone.utc).isoformat()


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def source_paths(project):
    """Keep project sources/configuration; discard old execution evidence."""
    result = []
    for directory, dirs, files in os.walk(project, followlinks=False):
        dirs[:] = sorted(d for d in dirs if d not in SKIP_DIRS)
        for filename in sorted(files):
            path = Path(directory) / filename
            relative = path.relative_to(project)
            if relative.parts[0] == "evidence" and relative != Path("evidence/declarations.json"):
                continue
            if filename == ".DS_Store" or path.suffix in BUILD_SUFFIXES:
                continue
            if path.is_symlink():
                raise RuntimeError(f"Source symlink requires explicit review: {path}")
            result.append(relative)
    return sorted(result)


def hashes(project):
    return {str(p): digest(project / p) for p in source_paths(project)}


def changed(before, after):
    return sorted(p for p in before.keys() | after.keys() if before.get(p) != after.get(p))


def capture(command, cwd=None, env=None):
    return subprocess.check_output(command, cwd=cwd, env=env, text=True, stderr=subprocess.STDOUT).strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", required=True, help="New output basename in publication/")
    parser.add_argument("--project", type=Path, default=WORKSPACE / "lean-controls")
    parser.add_argument("--baseline", type=Path, default=PUBLICATION / "final-fresh-replay.json")
    parser.add_argument("--dependency-cache", type=Path,
                        help="Default: isolated cache recorded in baseline manifest")
    args = parser.parse_args()
    if not re.fullmatch(r"[a-zA-Z0-9][a-zA-Z0-9_.-]*", args.prefix):
        parser.error("prefix must be a simple filename component")
    project = args.project.resolve()
    outputs = {kind: PUBLICATION / f"{args.prefix}{suffix}" for kind, suffix in {
        "manifest": ".json", "summary": ".txt", "log": ".log",
        "source_archive": ".sources.tar.gz", "build_log": ".build.log",
        "axioms_log": ".axioms.log", "axioms": ".axioms.json",
        "declarations": ".declarations.json"}.items()}
    existing = [str(p) for p in outputs.values() if p.exists()]
    if existing:
        parser.error("refusing to overwrite evidence: " + ", ".join(existing))
    report = {
        "status": "running", "started_utc": utc(), "original_project": str(project),
        "runner_path": str(Path(__file__).resolve()), "runner_sha256": digest(Path(__file__)),
        "mode": "fresh project-source check.sh replay; cached pinned dependencies and toolchain",
        "verification_scope": ["audit inventory freshness", "all project modules built from source",
                               "public theorem dependency-closure axiom audit"],
        "not_run": ["certificate producer tests", "certificate regeneration", "numerical design",
                    "physical validation", "bootstrap rebuild of Lean or dependency cache"],
        "axiom_allowlist": sorted(ALLOWED_AXIOMS),
    }
    started = time.monotonic()
    snapshot = None
    initial = None
    failure = None
    try:
        baseline_path = args.baseline.resolve()
        baseline = json.loads(baseline_path.read_text())
        cache = (args.dependency_cache or Path(baseline["dependency_cache_path"])).resolve()
        if not cache.is_dir():
            raise RuntimeError(f"Dependency cache does not exist: {cache}")
        if cache == (project / ".lake/packages").resolve():
            raise RuntimeError("Use an isolated dependency cache, not the original project's cache")
        report.update({"baseline_replay_manifest": str(baseline_path),
                       "baseline_manifest_sha256": digest(baseline_path),
                       "dependency_cache_path": str(cache),
                       "dependency_cache_method": "symlink to prior isolated dependency clone; may update dependency cache metadata",
                       "dependency_cache_read_only": False,
                       "original_project_build_products_reused": False})
        initial = hashes(project)
        report["original_source_sha256_before"] = initial
        report["snapshot_id_sha256"] = hashlib.sha256(
            json.dumps(initial, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
        scratch = Path(tempfile.mkdtemp(prefix=f"lean-controls-{args.prefix}-"))
        snapshot = scratch / "lean-controls"
        snapshot.mkdir()
        report["temporary_project"] = str(snapshot)
        for relative in initial:
            target = snapshot / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(project / relative, target)
        copied = hashes(snapshot)
        report["copied_source_sha256_before"] = copied
        report["source_file_count"] = len(copied)
        report["initial_project_build_exists"] = (snapshot / ".lake/build").exists()
        report["initial_project_olean_count"] = len(list(snapshot.rglob("*.olean")))
        if copied != initial or hashes(project) != initial:
            raise RuntimeError("Project changed while sources were copied, or copied hash mismatch")
        if report["initial_project_build_exists"] or report["initial_project_olean_count"]:
            raise RuntimeError("Fresh source snapshot unexpectedly contains project build products")
        with tarfile.open(outputs["source_archive"], "w:gz") as archive:
            for relative in initial:
                archive.add(snapshot / relative, arcname=f"lean-controls/{relative}", recursive=False)
        (snapshot / ".lake").mkdir()
        (snapshot / ".lake/packages").symlink_to(cache, target_is_directory=True)
        manifest = json.loads((snapshot / "lake-manifest.json").read_text())
        report["dependencies"] = manifest["packages"]
        heads, dirty = {}, {}
        for package in manifest["packages"]:
            if package["type"] != "git":
                raise RuntimeError(f"Unsupported dependency kind: {package}")
            directory = cache / package["name"]
            heads[package["name"]] = capture(["git", "rev-parse", "HEAD"], cwd=directory)
            dirty[package["name"]] = capture(
                ["git", "status", "--porcelain", "--untracked-files=no"], cwd=directory)
        report["dependency_checkout_heads_before"] = heads
        report["dependency_tracked_changes_before"] = dirty
        report["dependency_checkouts_match_manifest"] = all(
            heads[p["name"]] == p["rev"] for p in manifest["packages"])
        if not report["dependency_checkouts_match_manifest"] or any(dirty.values()):
            raise RuntimeError("Dependency checkout is modified or does not match its pinned revision")
        env = dict(os.environ)
        bundled = WORKSPACE / ".tools/elan"
        env.setdefault("ELAN_HOME", str(bundled if (bundled / "bin/lake").is_file()
                                        else Path.home() / ".elan"))
        lake = env.get("LAKE") or str(Path(env["ELAN_HOME"]) / "bin/lake")
        if not Path(lake).is_file():
            lake = shutil.which(lake) or shutil.which("lake")
        if not lake:
            raise RuntimeError("Lake not found; set ELAN_HOME or LAKE")
        env["LAKE"] = lake
        # Avoid inheriting paths that could resolve imports to the original project.
        report["removed_environment_variables"] = {}
        for variable in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "ELAN_TOOLCHAIN",
                         "LAKE_PACKAGE_CACHE_DIR", "LAKE_CACHE_DIR"):
            if variable in env:
                report["removed_environment_variables"][variable] = "removed for isolated replay"
                del env[variable]
        report.update({"lake_executable": lake, "elan_home": env["ELAN_HOME"],
                       "lean_toolchain": (snapshot / "lean-toolchain").read_text().strip(),
                       "lean_version": capture([lake, "env", "lean", "--version"], cwd=snapshot, env=env),
                       "replay_command": ["sh", "./check.sh"]})
        declarations = json.loads((snapshot / "evidence/declarations.json").read_text())
        modules = sorted(".".join(p.relative_to(snapshot).with_suffix("").parts)
                         for p in (snapshot / "LeanControls").rglob("*.lean"))
        report["expected_public_declarations"] = len(declarations)
        report["project_modules"] = modules
        report["expected_project_modules"] = len(modules)
        report["check_started_utc"] = utc()
        check_start = time.monotonic()
        with outputs["log"].open("w") as stream:
            completed = subprocess.run(["sh", "./check.sh"], cwd=snapshot, env=env,
                                       stdout=stream, stderr=subprocess.STDOUT)
        report.update({"check_exit_code": completed.returncode,
                       "check_elapsed_seconds": round(time.monotonic() - check_start, 3),
                       "check_finished_utc": utc()})
        if completed.returncode:
            raise RuntimeError(f"check.sh failed with exit code {completed.returncode}")
        audits = json.loads((snapshot / "evidence/axioms.json").read_text())
        report["public_declarations_audited"] = len(audits)
        report["unexpected_axioms"] = sorted(set().union(*map(set, audits.values())) - ALLOWED_AXIOMS)
        if set(audits) != {d["name"] for d in declarations} or report["unexpected_axioms"]:
            raise RuntimeError("Incomplete axiom audit or unexpected axiom")
        build_text = (snapshot / "evidence/build.log").read_text()
        built = sorted(set(re.findall(r"\bBuilt (LeanControls(?:\.[\w]+)*)\b", build_text)))
        expected_built = set(modules) | {"LeanControls"}
        report["project_modules_freshly_built"] = built
        report["missing_fresh_build_log_entries"] = sorted(expected_built - set(built))
        missing_artifacts = [m for m in expected_built if not
                             (snapshot / ".lake/build/lib/lean" / (m.replace(".", "/") + ".olean")).is_file()]
        report["missing_project_olean_files"] = sorted(missing_artifacts)
        if missing_artifacts or report["missing_fresh_build_log_entries"]:
            raise RuntimeError("Not every project module has evidence of a fresh build")
        report["aggregate_module_freshly_built"] = "LeanControls" in built
        heads_after = {p["name"]: capture(["git", "rev-parse", "HEAD"], cwd=cache / p["name"])
                       for p in manifest["packages"]}
        dirty_after = {p["name"]: capture(["git", "status", "--porcelain", "--untracked-files=no"],
                                         cwd=cache / p["name"])
                       for p in manifest["packages"]}
        report["dependency_checkout_heads_after"] = heads_after
        report["dependency_tracked_changes_after"] = dirty_after
        if heads_after != heads or any(dirty_after.values()):
            raise RuntimeError("Dependency source changed during replay")
        report["status"] = "passed"
    except Exception as exc:
        failure = f"{type(exc).__name__}: {exc}"
        report["status"] = "failed"
        report["error"] = failure
    finally:
        if initial is not None:
            after = hashes(project)
            report["original_source_sha256_after"] = after
            report["original_files_changed_since_snapshot"] = changed(initial, after)
            if snapshot is not None:
                copied_after = hashes(snapshot)
                report["copied_source_sha256_after"] = copied_after
                report["copied_source_hash_mismatches"] = changed(initial, copied_after)
                report["snapshot_files_unchanged_after_replay"] = copied_after == initial
            if report.get("original_files_changed_since_snapshot") or report.get("copied_source_hash_mismatches"):
                report["status"] = "failed"
                report["source_stability_error"] = "Source files changed during copy/replay"
        if snapshot is not None:
            for key, filename in {"build_log": "build.log", "axioms_log": "axioms.log",
                                  "axioms": "axioms.json", "declarations": "declarations.json"}.items():
                evidence = snapshot / "evidence" / filename
                if evidence.is_file():
                    shutil.copy2(evidence, outputs[key])
        report["completed_utc"] = utc()
        report["total_elapsed_seconds"] = round(time.monotonic() - started, 3)
        report["durable_artifacts"] = {key: {"path": str(path), "sha256": digest(path)}
                                       for key, path in outputs.items()
                                       if key not in {"manifest", "summary"} and path.is_file()}
        outputs["manifest"].write_text(json.dumps(report, indent=2) + "\n")
        summary = [f"FRESH SOURCE REPLAY: {report['status'].upper()}",
                   f"Project snapshot: {report.get('snapshot_id_sha256', 'not created')}",
                   f"Source files: {report.get('source_file_count', 0)}",
                   f"Project modules: {report.get('expected_project_modules', 0)}",
                   f"Public declarations audited: {report.get('public_declarations_audited', 0)}",
                   f"Check elapsed seconds: {report.get('check_elapsed_seconds', 'not run')}",
                   f"Temporary project retained: {report.get('temporary_project', 'not created')}",
                   "Pinned toolchain and isolated dependency cache were reused; this is not a bootstrap rebuild.",
                   "Only check.sh was replayed; producer tests and certificate regeneration were not run.",
                   f"Manifest: {outputs['manifest']}"]
        if failure:
            summary.append(f"Failure: {failure}")
        if "source_stability_error" in report:
            summary.append(report["source_stability_error"])
        outputs["summary"].write_text("\n".join(summary) + "\n")
        print("\n".join(summary), flush=True)
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    sys.exit(main())
