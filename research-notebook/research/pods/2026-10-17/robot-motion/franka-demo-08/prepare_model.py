"""Fetch a pinned, licensed model. No robot connection or controller install."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess

COMMIT = "62ab00f2bc44f6f20c1c9b7a13f3fb1dd41a4e35"
URL = "https://github.com/google-deepmind/mujoco_menagerie.git"


def main():
    p = argparse.ArgumentParser()
    p.add_argument("destination", type=Path)
    p.add_argument("--manifest", type=Path, required=True)
    a = p.parse_args()
    dest = a.destination.resolve()
    if not dest.exists():
        subprocess.run(["git", "clone", "--depth", "1", "--filter=blob:none", "--sparse", URL, str(dest)], check=True)
    remote = subprocess.check_output(["git", "-C", str(dest), "remote", "get-url", "origin"], text=True).strip()
    if remote != URL:
        raise SystemExit("Existing directory has a different origin; refusing to modify it")
    dirty = subprocess.check_output(["git", "-C", str(dest), "status", "--porcelain"], text=True)
    if dirty:
        raise SystemExit("Existing model checkout has local edits; refusing to modify it")
    subprocess.run(["git", "-C", str(dest), "fetch", "--depth", "1", "origin", COMMIT], check=True)
    subprocess.run(["git", "-C", str(dest), "sparse-checkout", "set", "franka_fr3", "franka_emika_panda"], check=True)
    subprocess.run(["git", "-C", str(dest), "checkout", "--detach", COMMIT], check=True)
    files = {}
    for name in ("franka_fr3", "franka_emika_panda"):
        for f in sorted((dest / name).rglob("*")):
            if f.is_file():
                files[str(f.relative_to(dest))] = hashlib.sha256(f.read_bytes()).hexdigest()
    a.manifest.write_text(json.dumps({"url": URL, "commit": COMMIT, "license": "Apache-2.0; see each model LICENSE", "files": files}, indent=2) + "\n")
    print(f"Pinned {len(files)} model files at {COMMIT}")


if __name__ == "__main__":
    main()
