"""Copy/run an isolated proof workspace through ctrl's existing Spark transport."""

import argparse
import base64
import json
import re
import shlex
from pathlib import Path, PurePosixPath

from ctrl import spark


def dispatch(action, run, workspace=None, model="leanstral:latest", minutes=20):
    if not re.fullmatch(r"ctrl-proofs-[a-zA-Z0-9-]+", run):
        raise ValueError("Expected ctrl-proofs-<unique-id>")
    if action == "upload":
        root = Path(workspace).resolve()
        files = {}
        for p in root.rglob("*"):
            if p.is_symlink():
                raise ValueError("Symlink in upload")
            if p.is_file() and ".git" not in p.parts and "__pycache__" not in p.parts:
                files[str(p.relative_to(root))] = base64.b64encode(p.read_bytes()).decode()
        payload = base64.b64encode(json.dumps(files).encode()).decode()
        script = """set -eu
export PATH="$HOME/.local/bin:$PATH"
uv run --no-project python - <<'PY'
import base64,json,pathlib
root=pathlib.Path.home()/'44-runs'/RUN
root.mkdir(parents=True,exist_ok=False)
files=json.loads(base64.b64decode(PAYLOAD))
for name,data in files.items():
    p=pathlib.PurePosixPath(name)
    assert not p.is_absolute() and '..' not in p.parts
    target=root/name
    target.parent.mkdir(parents=True,exist_ok=True)
    target.write_bytes(base64.b64decode(data))
print(json.dumps({'uploaded':str(root),'files':len(files)}))
PY
""".replace("RUN", repr(run)).replace("PAYLOAD", repr(payload))
    elif action == "fetch":
        destination = Path(workspace).resolve()
        if destination.exists():
            raise ValueError("Fetch destination exists; retain old evidence")
        script = """set -eu
export PATH="$HOME/.local/bin:$PATH"
uv run --no-project python - <<'PY'
import base64,json,pathlib
root=pathlib.Path.home()/'44-runs'/RUN
assert root.is_dir()
files={}
total=0
for p in root.rglob('*'):
    if p.is_file() and not p.is_symlink() and '.git' not in p.parts and '__pycache__' not in p.parts:
        data=p.read_bytes();total+=len(data)
        assert total<=32*1024*1024
        files[str(p.relative_to(root))]=base64.b64encode(data).decode()
print(json.dumps(files))
PY
""".replace("RUN", repr(run))
        cp = spark.ssh(script)
        if cp.returncode:
            raise RuntimeError(cp.stderr)
        files = json.loads(cp.stdout)
        for name in files:
            p = PurePosixPath(name)
            if p.is_absolute() or ".." in p.parts:
                raise ValueError("Unsafe fetch path")
        destination.mkdir(parents=True)
        for name, data in files.items():
            target = destination / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(base64.b64decode(data, validate=True))
        return {"destination": str(destination), "files": len(files)}
    else:
        body = (Path(__file__).resolve().parents[1] / "spark/factory.sh").read_text()
        script = "set -- " + " ".join(shlex.quote(str(x)) for x in (run, action, model, minutes))
        script += "\n" + body
    cp = spark.ssh(script, capture=action != "run")
    if cp.returncode:
        raise RuntimeError(cp.stderr or f"Remote operation exited {cp.returncode}")
    return {"action": action, "run": run, "output": cp.stdout}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["upload", "init", "preflight", "run", "status", "fetch"])
    parser.add_argument("run")
    parser.add_argument("--workspace")
    parser.add_argument("--model", default="leanstral:latest")
    parser.add_argument("--minutes", type=float, default=20)
    args = parser.parse_args()
    if args.action in ("upload", "fetch") and not args.workspace:
        parser.error("--workspace is required for upload/fetch")
    print(
        json.dumps(
            dispatch(args.action, args.run, args.workspace, args.model, args.minutes), indent=2
        )
    )
