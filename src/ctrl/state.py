"""Per-problem state, derived from files under work/NNN/ and lean/.

``status.json`` is written only by the CLI. Everything else (is the challenge approved, did it
drift, is the solution still a skeleton, is the last check stale) is recomputed from the files
on every call, so there is no hidden state to go out of sync.
"""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

from ctrl import fc
from ctrl.repo import Repo

PHASES = ("draft", "approved", "proving", "checked", "packaged")


def sha256(path: Path) -> str:
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load(repo: Repo, nnn: str) -> dict:
    f = repo.status_file(nnn)
    if not f.exists():
        return {}
    return json.loads(f.read_text())


def save(repo: Repo, nnn: str, status: dict) -> None:
    f = repo.status_file(nnn)
    f.parent.mkdir(parents=True, exist_ok=True)
    f.write_text(json.dumps(status, indent=2, ensure_ascii=False) + "\n")


def has_sorry(path: Path) -> bool:
    if not path.exists():
        return False
    return bool(re.search(r"(?<![\w'])sorry(?![\w'])", fc.strip_comments(path.read_text())))


def approval(repo: Repo, nnn: str, status: dict) -> dict:
    """Is the challenge approved, and does its hash still match? (check 5 in architecture.md)"""
    path = repo.challenge(nnn)
    if not path.exists():
        return {"ok": False, "approved": False, "detail": f"{repo.rel(path)} is missing"}
    line = fc.approval_line(path.read_text())
    expected = status.get("challenge_sha256")
    if not fc.is_approved_line(line) or not expected:
        return {"ok": False, "approved": False, "detail": "challenge not approved"}
    actual = sha256(path)
    if actual != expected:
        return {
            "ok": False,
            "approved": True,
            "detail": f"challenge changed after approval (sha256 {actual[:12]} ≠ {expected[:12]})",
            "expected": expected,
            "actual": actual,
        }
    return {"ok": True, "approved": True, "detail": line.removeprefix("-- ").strip()}


def summary(repo: Repo, nnn: str) -> dict:
    """One row for ``ctrl status``: the phase on disk, what the files say, and the next step."""
    st = load(repo, nnn)
    phase = st.get("phase", "draft")
    appr = approval(repo, nnn, st)
    sol = repo.solution(nnn)
    last = st.get("last_check") or {}
    stale = bool(last) and sol.exists() and last.get("solution_sha256") != sha256(sol)
    notes: list[str] = []
    nxt: list[str] = []
    if not repo.challenge(nnn).exists() or not sol.exists():
        notes.append("challenge or solution file missing")
        nxt = [f"ctrl new {nnn} --force"]
    elif appr["approved"] and not appr["ok"]:
        notes.append(appr["detail"])
        nxt = [f"git diff lean/Challenge/Erdos{nnn}.lean", f"ctrl approve {nnn} --by <name>"]
    elif not appr["approved"]:
        notes.append("waiting for a human to review the challenge statement")
        nxt = [f"ctrl approve {nnn} --by <name>"]
    elif phase == "checked" and not stale:
        if not st.get("last_spark_check", {}).get("ok"):
            nxt = [f"ctrl spark check {nnn}"]
        elif not (repo.workdir(nnn) / "disclosure.md").exists():
            notes.append(f"write work/{nnn}/disclosure.md")
            nxt = [f"$EDITOR work/{nnn}/disclosure.md"]
        else:
            nxt = [f"ctrl package {nnn}"]
    elif has_sorry(sol):
        notes.append("solution still has sorry")
        nxt = [f"ctrl spark prove {nnn}", f"ctrl check {nnn} --fast"]
    elif stale or not last:
        notes.append("solution changed since the last check" if stale else "never checked")
        nxt = [f"ctrl check {nnn}"]
    else:
        failed = [k for k in ("build", "tokens", "axioms", "binding", "hash") if not last.get(k)]
        notes.append("last check failed: " + ", ".join(failed) if failed else "last check failed")
        nxt = [f"ctrl check {nnn}"]
    return {
        "nnn": nnn,
        "phase": phase,
        "fc_theorem": st.get("fc_theorem", ""),
        "approved": appr["approved"],
        "hash_ok": appr["ok"],
        "last_check": last.get("at", ""),
        "last_check_ok": last.get("ok") if last else None,
        "stale": stale,
        "notes": notes,
        "next": nxt,
    }
