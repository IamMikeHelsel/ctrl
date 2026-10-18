#!/usr/bin/env python3
"""Copy research evidence without caches; check content hashes before committing.

Only files listed in the previous manifest may be updated. A changed destination
is a conflict. Files removed upstream are retained as historical evidence.
"""

import argparse
import hashlib
import json
import os
import subprocess
from pathlib import Path

ROOTS = (
    "AGENTS.md",
    "lean-research-report.html",
    "lean-controls",
    "publication",
    "research",
    "tmp",
)
SKIP_DIRS = {
    ".git",
    ".lake",
    ".tools",
    ".venv",
    "venv",
    "node_modules",
    "__pycache__",
    "media",
    ".cache",
    ".pytest_cache",
    ".ruff_cache",
    ".mypy_cache",
}
SKIP_SUFFIXES = (
    ".olean", ".ilean", ".ir", ".ir.sig", ".pyc", ".pyo", ".aux", ".out", ".cache-9"
)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def git(path, *args):
    return subprocess.check_output(["git", "-C", str(path), *args])


def ignored(path):
    return (
        any(x in SKIP_DIRS for x in path.parts)
        or path.name == ".DS_Store"
        or path.name.startswith("._")
        or ".olean." in path.name
        or path.name.endswith(SKIP_SUFFIXES)
    )


def collect(source):
    files = {}
    executable = {}
    vendors = []

    def add(src, relative):
        if src.is_symlink():
            raise RuntimeError(f"Refusing to follow source symlink: {src}")
        if not ignored(relative):
            files[relative.as_posix()] = src.read_bytes()
            executable[relative.as_posix()] = bool(src.stat().st_mode & 0o111)

    def vendor(path, relative):
        idx = len(vendors) + 1
        overlay = Path("_sync/overlays") / f"{idx:02d}-{path.name}"
        patch = git(
            path,
            "diff",
            "--no-ext-diff",
            "--no-color",
            "--binary",
            "--full-index",
            "HEAD",
        )
        untracked = git(path, "ls-files", "--others", "--exclude-standard", "-z").split(
            b"\0"
        )
        copied = []
        for name in untracked:
            if not name:
                continue
            local = Path(os.fsdecode(name))
            if ignored(local):
                continue
            add(path / local, overlay / "untracked" / local)
            copied.append(local.as_posix())
        if patch:
            files[(overlay / "working-tree.patch").as_posix()] = patch
        vendors.append(
            {
                "path": relative.as_posix(),
                "origin": git(path, "config", "--get", "remote.origin.url")
                .decode()
                .strip(),
                "commit": git(path, "rev-parse", "HEAD").decode().strip(),
                "overlay": overlay.as_posix() if patch or copied else None,
                "patch": "working-tree.patch" if patch else None,
                "untracked": sorted(copied),
            }
        )

    for name in ROOTS:
        start = source / name
        if start.is_file():
            add(start, Path(name))
        elif start.is_dir():
            for here, dirs, names in os.walk(start, followlinks=False):
                path = Path(here)
                relative = path.relative_to(source)
                if (path / ".git").exists():
                    vendor(path, relative)
                    dirs[:] = []
                    continue
                dirs[:] = sorted(d for d in dirs if not ignored(relative / d))
                for filename in sorted(names):
                    add(path / filename, relative / filename)
    files["_sync/nested-repositories.json"] = (
        json.dumps(vendors, indent=2) + "\n"
    ).encode()
    return files, vendors, executable


def safe_dest(destination, relative):
    rel = Path(relative)
    if rel.is_absolute() or ".." in rel.parts:
        raise RuntimeError(f"Invalid manifest path: {relative}")
    target = destination / rel
    current = target
    while current != destination:
        if current.is_symlink():
            raise RuntimeError(f"Refusing destination symlink: {current}")
        current = current.parent
    return target


def sync(source, destination, check=False):
    source, destination = source.resolve(), destination.resolve()
    if source == destination or source in destination.parents:
        raise RuntimeError("The destination must be outside the source workspace.")
    manifest_path = destination / "_sync/manifest.json"
    old = (
        json.loads(manifest_path.read_text())
        if manifest_path.exists()
        else {"files": {}}
    )
    files, vendors, executable = collect(source)
    records = {}
    changed = []
    conflicts = []
    for relative, data in files.items():
        target = safe_dest(destination, relative)
        expected = digest(data)
        actual = digest(target.read_bytes()) if target.exists() else None
        previous = old["files"].get(relative, {}).get("sha256")
        mode_matches = target.exists() and bool(
            target.stat().st_mode & 0o111
        ) == executable.get(relative, False)
        if actual != expected or not mode_matches:
            changed.append(relative)
            if actual is not None and actual != previous:
                conflicts.append(relative)
        records[relative] = {
            "sha256": expected,
            "bytes": len(data),
            "current_source": True,
            "executable": executable.get(relative, False),
        }
    # Preserve historical evidence removed or renamed in the source.
    for relative, record in old["files"].items():
        if relative in records:
            continue
        target = safe_dest(destination, relative)
        if not target.exists() or digest(target.read_bytes()) != record["sha256"]:
            conflicts.append(relative)
        records[relative] = {**record, "current_source": False}
    if conflicts:
        raise RuntimeError(
            "Destination changed independently; no files copied: "
            + ", ".join(conflicts)
        )
    manifest = {
        "schema": 1,
        "source_workspace": str(source),
        "scope": "Research sources, reports, evidence and final media; cached dependencies and generated caches excluded.",
        "nested_repository_count": len(vendors),
        "excluded_directories": sorted(SKIP_DIRS),
        "excluded_suffixes": list(SKIP_SUFFIXES) + [".olean.*"],
        "files": dict(sorted(records.items())),
    }
    serialized = (json.dumps(manifest, indent=2) + "\n").encode()
    manifest_changed = (
        not manifest_path.exists() or manifest_path.read_bytes() != serialized
    )
    if check:
        if changed or manifest_changed:
            raise RuntimeError(
                f"Notebook is out of date: {len(changed)} file differences; manifest_changed={manifest_changed}"
            )
    else:
        for relative in changed:
            target = safe_dest(destination, relative)
            target.parent.mkdir(parents=True, exist_ok=True)
            temporary = target.with_name(target.name + ".sync-tmp")
            temporary.write_bytes(files[relative])
            temporary.chmod(0o755 if records[relative]["executable"] else 0o644)
            os.replace(temporary, target)
        manifest_path.parent.mkdir(parents=True, exist_ok=True)
        manifest_path.write_bytes(serialized)
    # Check every recorded byte, including retained history.
    for relative, record in records.items():
        if digest(safe_dest(destination, relative).read_bytes()) != record["sha256"]:
            raise RuntimeError(f"Hash mismatch: {relative}")
    return {
        "checked": check,
        "files": len(records),
        "changed_files": len(changed),
        "bytes": sum(x["bytes"] for x in records.values()),
        "nested_repositories": len(vendors),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument(
        "--destination",
        type=Path,
        default=Path(__file__).resolve().parents[1] / "research-notebook",
    )
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    print(json.dumps(sync(args.source, args.destination, args.check), indent=2))


if __name__ == "__main__":
    main()
