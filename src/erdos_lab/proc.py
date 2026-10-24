"""The one place ctrl starts subprocesses (tests replace ``run``)."""

from __future__ import annotations

import os
import shutil
import subprocess
from pathlib import Path


def run(
    cmd: list[str],
    *,
    cwd: Path | None = None,
    input: str | None = None,
    capture: bool = True,
    timeout: float | None = None,
) -> subprocess.CompletedProcess:
    """Run ``cmd``. With ``capture=False`` stdout/stderr stream through (used by ``log -f``)."""
    return subprocess.run(
        cmd,
        cwd=cwd,
        input=input,
        text=True,
        capture_output=capture,
        timeout=timeout,
        check=False,
    )


def which(name: str, *extra_dirs: str) -> str | None:
    """``shutil.which`` plus well-known install dirs that non-login shells miss (e.g. ~/.elan/bin)."""
    found = shutil.which(name)
    if found:
        return found
    for d in extra_dirs:
        p = Path(os.path.expanduser(d)) / name
        if p.is_file() and os.access(p, os.X_OK):
            return str(p)
    return None
