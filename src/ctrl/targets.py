"""Ranked target rows from data/erdos/{open,formalize}.csv."""

from __future__ import annotations

import csv

from ctrl.errors import CtrlError, usage
from ctrl.repo import Repo

TABS = ("open", "formalize")
# per tab: (difficulty column, fit column, sort key)
COLUMNS = {
    "open": ("difficulty_1to5", "ai_lean_fit_1to5"),
    "formalize": ("formalization_effort_1to5", "priority_1to5"),
}
INT_COLS = {
    "erdos_no",
    "prize_usd_approx",
    "difficulty_1to5",
    "ai_lean_fit_1to5",
    "tractability_score",
    "priority_1to5",
    "formalization_effort_1to5",
    "comments",
}


def _int(v: str) -> int | None:
    try:
        return int(float(v))
    except (TypeError, ValueError):
        return None


def load(repo: Repo, tab: str) -> list[dict]:
    if tab not in TABS:
        raise usage(f"unknown tab {tab!r}", fix="ctrl targets --tab formalize")
    path = repo.root / "data" / "erdos" / f"{tab}.csv"
    if not path.exists():
        raise CtrlError("TOOL_MISSING", f"{repo.rel(path)} is missing", fix="git status data/")
    with path.open(newline="", encoding="utf-8") as f:
        rows = list(csv.DictReader(f))
    for r in rows:
        for k in INT_COLS & r.keys():
            r[k] = _int(r[k])
        r["has_fc"] = r.get("lean_statement_in_formal_conjectures") == "yes"
    return rows


def sort_key(tab: str):
    if tab == "open":
        return lambda r: (
            -(r.get("tractability_score") or 0),
            -(r.get("ai_lean_fit_1to5") or 0),
            r.get("difficulty_1to5") or 9,
            -(r.get("prize_usd_approx") or 0),
            r.get("erdos_no") or 0,
        )
    return lambda r: (
        -(r.get("priority_1to5") or 0),
        r.get("formalization_effort_1to5") or 9,
        -(r.get("prize_usd_approx") or 0),
        r.get("erdos_no") or 0,
    )


def select(
    rows: list[dict],
    tab: str,
    *,
    top: int = 20,
    prize: bool = False,
    max_difficulty: int | None = None,
    min_fit: int | None = None,
) -> list[dict]:
    diff_col, fit_col = COLUMNS[tab]
    out = []
    for r in rows:
        if prize and not (r.get("prize_usd_approx") or 0) > 0:
            continue
        if max_difficulty is not None and (r.get(diff_col) or 9) > max_difficulty:
            continue
        if min_fit is not None and (r.get(fit_col) or 0) < min_fit:
            continue
        out.append(r)
    out.sort(key=sort_key(tab))
    return out[: max(0, top)] if top else out
