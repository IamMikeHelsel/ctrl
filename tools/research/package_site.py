"""Package only the reviewed research site files; never publish a workspace tree."""

import hashlib
import json
import shutil
from pathlib import Path
from zipfile import ZIP_DEFLATED, ZipFile

ROOT = Path(__file__).resolve().parents[2]
SITE = ROOT / "site"
DEST = ROOT / "output/ctrl-research-site-2026-10-21"
FILES = [
    "index.html",
    "style.css",
    "favicon.svg",
    "research.html",
    "research.css",
    "research.js",
    "research.json",
    "AGENT_IDEA_INDEX.json",
    "studies/latency-braking.html",
    "studies/latency-braking.js",
    "studies/transport.html",
    "assets/research/manifest.json",
    "assets/research/latency-braking.mp4",
    "assets/research/latency-braking-poster.png",
]


def main():
    manifest = json.loads((SITE / "assets/research/manifest.json").read_text())
    names = FILES + ["assets/research/" + row["file"] for row in manifest["artifacts"]]
    assert len(names) == len(set(names))
    records = []
    for name in names:
        source = SITE / name
        target = DEST / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        records.append({"path": name, "sha256": hashlib.sha256(source.read_bytes()).hexdigest()})
    package = {
        "status": "local review snapshot; not deployed",
        "as_of": "2026-10-21",
        "contents": "Allowlisted research pages and curated artifacts only",
        "files": records,
    }
    package_manifest = DEST / "package-manifest.json"
    package_manifest.write_text(json.dumps(package, indent=2) + "\n")
    archive = DEST.with_suffix(".zip")
    with ZipFile(archive, "w", compression=ZIP_DEFLATED) as bundle:
        for name in names + ["package-manifest.json"]:
            bundle.write(DEST / name, arcname=name)
    with ZipFile(archive) as bundle:
        assert bundle.testzip() is None
        assert set(bundle.namelist()) == set(names + ["package-manifest.json"])
        for row in records:
            assert hashlib.sha256(bundle.read(row["path"])).hexdigest() == row["sha256"]
    print(f"{len(names)} files + manifest packaged and hash-verified: {archive}")


if __name__ == "__main__":
    main()
