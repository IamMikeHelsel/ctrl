"""Linux-only Lean sandbox backend for an isolated 44 workspace."""

import json
import os
import resource
import subprocess
import sys
from pathlib import Path


def sandbox(command, root, project, writable=True):
    if sys.platform != "linux":
        raise RuntimeError("Live acceptance requires Linux bubblewrap")
    config = json.loads((root / "reference/runtime.json").read_text())
    cache = Path(config["lean_project"])
    chain = Path(config["toolchain"])
    paths = []
    for path in config["lean_path"].split(":"):
        p = Path(path)
        if p.is_relative_to(cache):
            paths.append("/cache/" + str(p.relative_to(cache)))
        elif p.is_relative_to(chain):
            paths.append("/toolchain/" + str(p.relative_to(chain)))
        else:
            raise ValueError(f"Unexpected Lean dependency path: {p}")
    return [
        "bwrap",
        "--die-with-parent",
        "--new-session",
        "--unshare-all",
        "--ro-bind",
        "/usr",
        "/usr",
        "--symlink",
        "usr/lib",
        "/lib",
        "--symlink",
        "usr/bin",
        "/bin",
        "--proc",
        "/proc",
        "--dev",
        "/dev",
        "--tmpfs",
        "/tmp",
        "--dir",
        "/home",
        "--ro-bind",
        str(chain),
        "/toolchain",
        "--ro-bind",
        str(cache),
        "/cache",
        "--ro-bind",
        str(project),
        "/project",
        "--ro-bind",
        str(root / "acceptance"),
        "/acceptance",
        "--bind" if writable else "--ro-bind",
        str(root / "build"),
        "/build",
        "--chdir",
        "/project",
        "--clearenv",
        "--setenv",
        "PATH",
        "/usr/bin:/bin",
        "--setenv",
        "HOME",
        "/tmp",
        "--setenv",
        "LEAN_PATH",
        ":".join(paths),
    ] + command


def limits():
    os.nice(10)
    # Mathlib maps more than 8 GiB of address space; resident RAM is much smaller.
    resource.setrlimit(resource.RLIMIT_AS, (32 * 1024**3, 32 * 1024**3))
    resource.setrlimit(resource.RLIMIT_CPU, (95, 95))
    resource.setrlimit(resource.RLIMIT_FSIZE, (16 * 1024**2, 16 * 1024**2))
    resource.setrlimit(resource.RLIMIT_NOFILE, (8192, 8192))


def check(stage, root, project):
    (root / "build").mkdir(exist_ok=True)
    cp = subprocess.run(
        sandbox(["/usr/bin/python3", "/acceptance/check.py", str(stage)], root, project),
        capture_output=True,
        text=True,
        timeout=110,
        preexec_fn=limits,
    )
    text = cp.stdout + cp.stderr
    return cp.returncode == 0 and f"ACCEPTANCE_STAGE_{stage}_PASS" in text, text[-20000:]
