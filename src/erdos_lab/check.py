"""The five checks of architecture.md, aggregated.

Checks 1-4 (build, forbidden tokens, axioms, statement binding) come from
``erdos/scripts/check.sh NNN [--fast]``, which prints one JSON object. Check 5 (the challenge
carries an approval and its sha256 still matches status.json) is computed here.
"""

from __future__ import annotations

import json
from datetime import UTC, datetime

from erdos_lab import proc, state
from erdos_lab.errors import EXIT_FAILED_CHECK, EXIT_NEEDS_HUMAN, CtrlError
from erdos_lab.repo import Repo

CHECKS = (
    ("build", "LEAN_BUILD_FAILED"),
    ("tokens", "FORBIDDEN_TOKEN"),
    ("axioms", "NONSTANDARD_AXIOM"),
    ("binding", "BINDING_MISMATCH"),
    ("hash", "CHALLENGE_DRIFT"),
)
LOG_TAIL = 4000


def parse_report(stdout: str, stderr: str = "", returncode: int = 0) -> dict:
    """check.sh's JSON. Anything else is reported as a failed build with the output as the log."""
    text = (stdout or "").strip()
    report = None
    for candidate in (text, *reversed(text.splitlines())):
        try:
            obj = json.loads(candidate)
        except (json.JSONDecodeError, ValueError):
            continue
        if isinstance(obj, dict):
            report = obj
            break
    if report is None:
        log = ((stderr or "") + "\n" + (stdout or "")).strip()
        return {
            "build": {
                "ok": False,
                "log": log[-LOG_TAIL:] or f"check.sh exited {returncode} with no output",
            }
        }
    return report


def run_local(repo: Repo, nnn: str, fast: bool) -> dict:
    script = repo.lean / "scripts" / "check.sh"
    if not script.exists():
        raise CtrlError(
            "TOOL_MISSING",
            "erdos/scripts/check.sh is missing",
            hint="erdos check runs checks 1-4 through that script",
            fix="git status erdos/scripts",
        )
    cmd = ["bash", "scripts/check.sh", nnn] + (["--fast"] if fast else [])
    cp = proc.run(cmd, cwd=repo.lean)
    script_errors(cp, "erdos/scripts/check.sh")
    return parse_report(cp.stdout, cp.stderr, cp.returncode)


def script_errors(cp, name: str) -> None:
    """check.sh exits 1 when lake is missing and 2 on bad usage; neither is a check result."""
    if cp.returncode not in (1, 2):
        return
    obj = None
    try:
        obj = json.loads((cp.stdout or "").strip().splitlines()[-1])
    except (json.JSONDecodeError, IndexError):
        pass
    if isinstance(obj, dict) and {"build", "tokens", "axioms", "binding"} & obj.keys():
        return  # a real report, whatever the exit code
    detail = (obj or {}).get("error") if isinstance(obj, dict) else None
    detail = detail or ((cp.stderr or cp.stdout or "").strip().splitlines() or [""])[-1]
    if cp.returncode == 1:
        raise CtrlError(
            "TOOL_MISSING",
            f"{name}: {detail or 'lake not found'}",
            hint="the Lean toolchain is not usable here",
            fix="erdos doctor --no-remote",
        )
    raise CtrlError(
        "BAD_USAGE", f"{name} rejected its arguments: {detail}", exit_code=2, fix="erdos --help"
    )


def result(repo: Repo, nnn: str, report: dict) -> dict:
    """One row of ``results``: the four script checks plus the hash check, each ``{ok, ...}``."""
    st = state.load(repo, nnn)
    row: dict = {"nnn": nnn}
    for key, _code in CHECKS[:-1]:
        entry = report.get(key)
        if not isinstance(entry, dict) or "ok" not in entry:
            entry = {"ok": False, "detail": f"check.sh did not report `{key}`"}
        if isinstance(entry.get("log"), str) and len(entry["log"]) > LOG_TAIL:
            entry = {**entry, "log": entry["log"][-LOG_TAIL:]}
        row[key] = {**entry, "ok": bool(entry["ok"])}
    row["hash"] = state.approval(repo, nnn, st)
    row["ok"] = all(row[k]["ok"] for k, _ in CHECKS)
    row["failed"] = failed_codes(row)
    return row


def failed_codes(row: dict) -> list[str]:
    codes = []
    for key, code in CHECKS:
        if not row[key]["ok"]:
            if key == "hash" and not row[key].get("approved"):
                codes.append("NOT_APPROVED")
            else:
                codes.append(code)
    return codes


MESSAGES = {
    "LEAN_BUILD_FAILED": "the Lean build failed",
    "FORBIDDEN_TOKEN": "the solution uses a forbidden token",
    "NONSTANDARD_AXIOM": "the solution depends on a non-standard axiom",
    "BINDING_MISMATCH": "the solution does not prove Challenge.ErdosNNN.statement",
    "CHALLENGE_DRIFT": "the challenge changed after it was approved",
}


def error_for(rows: list[dict]) -> CtrlError | None:
    """Exit 4 if any real check failed; else exit 3 if something is only unapproved; else None."""
    for row in rows:
        for code in row["failed"]:
            if code == "NOT_APPROVED":
                continue
            nnn = row["nnn"]
            key = next(k for k, c in CHECKS if c == code)
            detail = row[key].get("detail") or ""
            if code == "LEAN_BUILD_FAILED":
                detail = (row[key].get("log") or "").strip().splitlines()[-1:] or [""]
                detail = detail[0]
            elif code == "FORBIDDEN_TOKEN":
                detail = ", ".join(map(str, row[key].get("hits") or [])) or detail
            elif code == "NONSTANDARD_AXIOM":
                detail = ", ".join(map(str, row[key].get("axioms") or [])) or detail
            fix = (
                f"git diff erdos/Challenge/Erdos{nnn}.lean   # restore it, or a human re-approves"
                if code == "CHALLENGE_DRIFT"
                else f"erdos check {nnn} --fast"
            )
            return CtrlError(
                code,
                f"{nnn}: " + MESSAGES[code].replace("NNN", nnn),
                hint=str(detail)[:500],
                fix=fix,
                exit_code=EXIT_FAILED_CHECK,
            )
    for row in rows:
        if "NOT_APPROVED" in row["failed"]:
            nnn = row["nnn"]
            return CtrlError(
                "NOT_APPROVED",
                f"{nnn}: the challenge statement is not approved",
                hint="a human must review erdos/Challenge/Erdos" + nnn + ".lean first",
                fix=f"erdos approve {nnn} --by <name>",
                exit_code=EXIT_NEEDS_HUMAN,
            )
    return None


def record(repo: Repo, nnn: str, row: dict, *, fast: bool, where: str = "local") -> None:
    """Write the result into work/NNN/status.json (and move the phase for local checks)."""
    st = state.load(repo, nnn) or {"nnn": nnn, "phase": "draft"}
    sol = repo.solution(nnn)
    entry = {
        "at": datetime.now(UTC).isoformat(timespec="seconds"),
        "fast": fast,
        "ok": row["ok"],
        **{k: row[k]["ok"] for k, _ in CHECKS},
        "failed": row["failed"],
        "solution_sha256": state.sha256(sol) if sol.exists() else "",
    }
    if where == "spark":
        st["last_spark_check"] = entry
    else:
        st["last_check"] = entry
        if row["hash"]["ok"] and st.get("phase") in ("approved", "proving", "checked"):
            st["phase"] = "checked" if row["ok"] and not fast else "proving"
    state.save(repo, nnn, st)
