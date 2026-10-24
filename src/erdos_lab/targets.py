"""Ranked target rows from {open,formalize}.csv.

The CSVs are generated (tools/erdos-assess) and live outside git. Lookup order:
``$ERDOS_DATA_DIR``, then ``<repo>/data/erdos``, then the Drive copy
``~/Library/CloudStorage/GoogleDrive-*/My Drive/lean/erdos-data``.
"""

from __future__ import annotations

import csv
import os
from pathlib import Path

from erdos_lab.errors import CtrlError, usage
from erdos_lab.repo import Repo

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


def data_dirs(repo: Repo) -> list[Path]:
    dirs = []
    if os.environ.get("ERDOS_DATA_DIR"):
        dirs.append(Path(os.environ["ERDOS_DATA_DIR"]).expanduser())
    dirs.append(repo.root / "data" / "erdos")
    dirs += sorted(Path.home().glob("Library/CloudStorage/GoogleDrive-*/My Drive/lean/erdos-data"))
    return dirs


def load(repo: Repo, tab: str) -> list[dict]:
    if tab not in TABS:
        raise usage(f"unknown tab {tab!r}", fix="erdos targets --tab formalize")
    dirs = data_dirs(repo)
    path = next((d / f"{tab}.csv" for d in dirs if (d / f"{tab}.csv").exists()), None)
    if path is None:
        raise CtrlError(
            "TOOL_MISSING",
            f"{tab}.csv not found (looked in {', '.join(str(d) for d in dirs)})",
            hint="the target CSVs are generated data kept in Drive (lean/erdos-data), not in git",
            fix="export ERDOS_DATA_DIR=<folder with open.csv and formalize.csv>",
        )
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
