"""Talking to the Spark: rsync the repo over, run tools/spark/*.sh over ssh, read job dirs.

This is the only module that builds ssh/rsync command lines (docs/erdos-lab/rules.md: don't hand-roll ssh
elsewhere). Remote scripts are sent to ``bash -s`` on stdin, so the remote login shell (zsh on
the Spark) and its quoting rules never matter.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import shlex
import subprocess

from erdos_lab import proc
from erdos_lab.errors import EXIT_NEEDS_HUMAN, EXIT_REMOTE, CtrlError, usage
from erdos_lab.repo import Repo

SSH_OPTS = ["-o", "BatchMode=yes", "-o", "ConnectTimeout=8"]
REMOTE_REPO = "lean-work/ctrl"  # relative to the remote home
REMOTE_JOBS = "lean-work/jobs"
EXCLUDES = [".lake", ".git", ".venv"]
JOB_RE = re.compile(r"[A-Za-z0-9][A-Za-z0-9._-]{0,127}")
MISSING = 44  # remote snippet exit code: the thing asked about doesn't exist


def host() -> str:
    return os.environ.get("SPARK_SSH_HOST") or "sparky.local"


def unreachable(detail: str = "") -> CtrlError:
    h = host()
    return CtrlError(
        "SPARK_UNREACHABLE",
        f"can't reach the Spark at {h}",
        hint=(detail.strip().splitlines() or ["ssh failed"])[-1],
        fix=f"ssh {h} true   # or set SPARK_SSH_HOST",
        exit_code=EXIT_REMOTE,
    )


def _need(tool: str) -> str:
    path = proc.which(tool)
    if not path:
        raise CtrlError("TOOL_MISSING", f"`{tool}` is not on PATH", fix=f"install {tool}")
    return path


def ssh(script: str, *, capture: bool = True) -> subprocess.CompletedProcess:
    """Run a bash script on the Spark. ssh's own failure (exit 255) means unreachable."""
    _need("ssh")
    cp = proc.run(["ssh", *SSH_OPTS, host(), "bash", "-s"], input=script, capture=capture)
    if cp.returncode == 255:
        raise unreachable(cp.stderr or "")
    return cp


def check_job_id(job: str) -> str:
    if not JOB_RE.fullmatch(job):
        raise usage(f"not a job id: {job!r}", fix="erdos spark jobs")
    return job


def job_not_found(job: str) -> CtrlError:
    return CtrlError(
        "JOB_NOT_FOUND",
        f"no job {job} on {host()}",
        hint=f"looked in ~/{REMOTE_JOBS}/{job}/",
        fix="erdos spark jobs",
        exit_code=EXIT_REMOTE,
    )


# ------------------------------------------------------------------ sync


def rsync_cmd(repo: Repo) -> list[str]:
    cmd = ["rsync", "-az", "-i", "--delete"]
    for e in EXCLUDES:
        cmd += ["--exclude", e]
    cmd += [
        "-e",
        "ssh " + " ".join(SSH_OPTS),
        f"--rsync-path=mkdir -p {REMOTE_REPO} && rsync",
        f"{repo.root}/",
        f"{host()}:{REMOTE_REPO}/",
    ]
    return cmd


def parse_itemized(out: str) -> list[str]:
    """Files rsync -i reports as sent or deleted (directory entries skipped)."""
    changed = []
    for line in out.splitlines():
        if line.startswith("*deleting"):
            changed.append(line.split(None, 1)[1].strip())
            continue
        parts = line.split(None, 1)
        if len(parts) != 2 or len(parts[0]) < 2:
            continue
        flags, path = parts
        if flags[0] in "<>ch" and flags[1] != "d":
            changed.append(path.strip())
    return changed


CACHE_SCRIPT = """\
set -e
cd ~/{repo}/erdos
if [ "{force}" = 1 ] || [ ! -d .lake/packages/mathlib ]; then
  source ~/.elan/env
  lake exe cache get 1>&2
  echo ran
fi
"""


def sync(repo: Repo, *, force: bool = False) -> dict:
    """rsync the repo to the Spark; fetch the Mathlib cache if the manifest changed.

    Running prove jobs share the repo copy's .lake/packages through a symlink, so a sync that
    changes erdos/lake-manifest.json (and so re-runs `lake exe cache get`) is refused while one runs.
    """
    _need("rsync")
    if not force:
        running, remote_sha = presync()
        local = repo.lean / "lake-manifest.json"
        local_sha = hashlib.sha256(local.read_bytes()).hexdigest() if local.exists() else ""
        if running and remote_sha and remote_sha != local_sha:
            ids = ", ".join(str(r.get("job")) for r in running)
            raise CtrlError(
                "JOB_RUNNING",
                f"prove job(s) running on {host()} ({ids}) and this sync would change "
                "erdos/lake-manifest.json",
                hint="prove jobs share the repo copy's .lake/packages; wait for them, or pass --force",
                fix="erdos spark jobs",
                exit_code=EXIT_NEEDS_HUMAN,
            )
    cp = proc.run(rsync_cmd(repo))
    if cp.returncode != 0:
        raise unreachable(cp.stderr or f"rsync exited {cp.returncode}")
    changed = parse_itemized(cp.stdout or "")
    manifest = "erdos/lake-manifest.json" in changed
    cache = ssh(CACHE_SCRIPT.format(repo=REMOTE_REPO, force=int(manifest)))
    if cache.returncode != 0:
        raise CtrlError(
            "REMOTE_FAILED",
            "`lake exe cache get` failed on the Spark",
            hint=((cache.stderr or "").strip().splitlines() or ["no output"])[-1],
            fix=f"ssh {host()} 'cd ~/{REMOTE_REPO}/erdos && source ~/.elan/env && lake exe cache get'",
        )
    return {
        "host": host(),
        "changed": changed,
        "manifest_changed": manifest,
        "cache_fetched": "ran" in (cache.stdout or ""),
    }


# ------------------------------------------------------------------ scripts and jobs


def script_cmd(name: str, args: list[str], env: dict[str, str] | None = None) -> str:
    path = f"~/{REMOTE_REPO}/tools/spark/{name}.sh"
    prefix = "".join(f"{k}={shlex.quote(str(v))} " for k, v in (env or {}).items())
    return (
        f'f={path}; [ -f "$f" ] || {{ echo "missing $f" >&2; exit 127; }}\n'
        f'{prefix}bash "$f" {" ".join(shlex.quote(a) for a in args)}\n'
    )


def run_script(
    name: str, args: list[str], env: dict[str, str] | None = None, *, capture: bool = True
) -> subprocess.CompletedProcess:
    cp = ssh(script_cmd(name, args, env), capture=capture)
    if cp.returncode == 127:
        raise CtrlError(
            "TOOL_MISSING",
            f"tools/spark/{name}.sh is missing on the Spark",
            hint=(cp.stderr or "").strip(),
            fix="erdos spark sync",
        )
    return cp


def last_json(stdout: str) -> dict | None:
    for line in reversed((stdout or "").splitlines()):
        line = line.strip()
        if line.startswith("{"):
            try:
                return json.loads(line)
            except json.JSONDecodeError:
                continue
    return None


def remote_failed(name: str, cp: subprocess.CompletedProcess) -> CtrlError:
    tail = ((cp.stderr or "") + (cp.stdout or "")).strip().splitlines()[-5:]
    return CtrlError(
        "REMOTE_FAILED",
        f"tools/spark/{name}.sh failed on the Spark (exit {cp.returncode})",
        hint=" | ".join(tail) or "no output",
        fix="erdos doctor --remote",
    )


def start_job(name: str, args: list[str], env: dict[str, str] | None = None) -> str:
    cp = run_script(name, args, env)
    obj = last_json(cp.stdout)
    if cp.returncode != 0 or not obj or not obj.get("job"):
        raise remote_failed(name, cp)
    return str(obj["job"])


RUNNING = ("running", "starting")


def parse_jobs(stdout: str) -> list[dict]:
    try:
        rows = json.loads(stdout or "[]")
    except json.JSONDecodeError as exc:
        raise CtrlError(
            "REMOTE_FAILED", "tools/spark/jobs.sh did not print JSON", hint=str(exc)
        ) from exc
    return [r for r in rows if isinstance(r, dict)] if isinstance(rows, list) else []


def jobs() -> list[dict]:
    """tools/spark/jobs.sh: every meta.json, newest first (status running|success|failed|...)."""
    cp = run_script("jobs", [])
    if cp.returncode != 0:
        raise remote_failed("jobs", cp)
    return parse_jobs(cp.stdout)


PRESYNC_SCRIPT = f"""\
j=~/{REMOTE_REPO}/tools/spark/jobs.sh
if [ -f "$j" ]; then bash "$j" 2>/dev/null || echo '[]'; else echo '[]'; fi
echo '@@manifest@@'
sha256sum ~/{REMOTE_REPO}/erdos/lake-manifest.json 2>/dev/null | cut -d' ' -f1
"""


def presync() -> tuple[list[dict], str]:
    """(running prove jobs, remote lake-manifest sha256) in one ssh call."""
    cp = ssh(PRESYNC_SCRIPT)
    out = cp.stdout or ""
    jobs_text, _, sha = out.partition("@@manifest@@")
    try:
        rows = parse_jobs(jobs_text.strip())
    except CtrlError:
        rows = []
    running = [r for r in rows if r.get("kind") == "prove" and r.get("status") in RUNNING]
    return running, sha.strip()


def meta(job: str) -> dict:
    cp = ssh(f'f=~/{REMOTE_JOBS}/{job}/meta.json; [ -f "$f" ] || exit {MISSING}; cat "$f"\n')
    if cp.returncode == MISSING:
        raise job_not_found(job)
    try:
        return json.loads(cp.stdout)
    except json.JSONDecodeError as exc:
        raise CtrlError(
            "REMOTE_FAILED", f"meta.json for job {job} is not JSON", hint=str(exc)
        ) from exc


def log(job: str, lines: int, follow: bool) -> subprocess.CompletedProcess:
    """tools/spark/log.sh JOB [-f] -n N: -f streams and returns when the job ends; exit 5 = missing."""
    args = [job, "-n", str(int(lines))] + (["-f"] if follow else [])
    cp = run_script("log", args, capture=not follow)
    if cp.returncode == 5:
        raise job_not_found(job)
    if cp.returncode != 0 and not follow:
        raise remote_failed("log", cp)
    return cp


def fetch(job: str, dest) -> list[str]:
    _need("rsync")
    dest.mkdir(parents=True, exist_ok=True)
    cmd = [
        "rsync",
        "-az",
        "-i",
        "-e",
        "ssh " + " ".join(SSH_OPTS),
        f"{host()}:{REMOTE_JOBS}/{job}/outputs/",
        f"{dest}/",
    ]
    cp = proc.run(cmd)
    if cp.returncode != 0:
        if "No such file" in (cp.stderr or ""):
            raise CtrlError(
                "JOB_NOT_FOUND",
                f"job {job} has no outputs/ yet",
                hint=(cp.stderr or "").strip().splitlines()[-1],
                fix=f"erdos spark log {job}",
                exit_code=EXIT_REMOTE,
            )
        raise unreachable(cp.stderr or f"rsync exited {cp.returncode}")
    return parse_itemized(cp.stdout or "")
