"""Terminal UI: one result, three renderings.

* **rich**: a human at a terminal. Color and tables.
* **plain**: pipes, CI, and agents (chosen when ``CLAUDECODE`` or ``CTRL_AGENT`` is set, or
  stdout is not a TTY). Same content, no color, stable line-oriented layout.
* **json**: ``--json`` or ``CTRL_JSON=1``. Exactly one envelope on stdout:
  ``{"ok", "command", "data", "warnings", "next", "error"}``. Progress goes to stderr.

Every command ends with ``finish(data, render, next=[...])``: the exact commands that move
things forward, so neither a person nor an agent has to guess.
"""

from __future__ import annotations

import json
import os
import sys
from collections.abc import Callable
from dataclasses import dataclass, field

from rich import box
from rich.console import Console, Group, RenderableType
from rich.table import Table
from rich.text import Text

from ctrl.errors import CtrlError

ACCENT = "#5fd7d7"
OK = "#87d787"
WARN = "#ffd75f"
BAD = "#ff8787"
DIM = "#808080"

AGENT_ENV = ("CLAUDECODE", "CLAUDE_CODE", "CTRL_AGENT")


@dataclass
class UIState:
    mode: str = "rich"  # rich | plain | json
    command: str = ""
    out: Console = field(default_factory=Console)
    err: Console = field(default_factory=lambda: Console(stderr=True))

    @property
    def json(self) -> bool:
        return self.mode == "json"

    @property
    def rich(self) -> bool:
        return self.mode == "rich"


ui = UIState()


def configure(*, json_mode: bool = False, plain: bool = False) -> UIState:
    agent = any(os.environ.get(k) for k in AGENT_ENV)
    if json_mode or os.environ.get("CTRL_JSON") == "1":
        mode = "json"
    elif plain or agent or not sys.stdout.isatty():
        mode = "plain"
    else:
        mode = "rich"
    flat = mode != "rich"
    ui.mode = mode
    ui.command = ""
    ui.out = Console(no_color=flat, highlight=False, soft_wrap=flat, width=120 if flat else None)
    ui.err = Console(stderr=True, no_color=flat, highlight=False)
    return ui


# ------------------------------------------------------------------ results


def envelope(
    data: dict | None,
    *,
    next: list[str] | None = None,
    warnings: list[str] | None = None,
    error: CtrlError | None = None,
) -> dict:
    return {
        "ok": error is None,
        "command": ui.command,
        "data": data,
        "warnings": list(warnings or []),
        "next": list(next or []),
        "error": error.to_dict() if error else None,
    }


def finish(
    data: dict,
    render: Callable[[dict], RenderableType | None] | None = None,
    *,
    next: list[str] | None = None,
    warnings: list[str] | None = None,
    error: CtrlError | None = None,
) -> None:
    """Print the result. With ``error``, the data is still shown and the process exits non-zero."""
    if ui.json:
        env = envelope(data, next=next, warnings=warnings, error=error)
        sys.stdout.write(json.dumps(env, indent=1, ensure_ascii=False, default=str) + "\n")
        sys.stdout.flush()
    else:
        if render is not None:
            body = render(data)
            if body is not None:
                ui.out.print(body)
        for w in warnings or []:
            ui.out.print(Text.assemble(("  ! ", WARN), (w, WARN)))
        if error is not None:
            ui.err.print(error_block(error))
        if next:
            ui.out.print(next_block(next))
    if error is not None:
        raise SystemExit(error.exit_code)


def fail(err: CtrlError) -> None:
    if ui.json:
        env = envelope(None, next=[err.fix] if err.fix else [], error=err)
        sys.stdout.write(json.dumps(env, indent=1, ensure_ascii=False) + "\n")
        sys.stdout.flush()
    else:
        ui.err.print(error_block(err))
    raise SystemExit(err.exit_code)


def error_block(err: CtrlError) -> Group:
    lines = [Text.assemble(("✕ ", BAD), (err.message, "bold"))]
    if err.hint:
        lines.append(Text.assemble(("  why  ", DIM), err.hint))
    if err.fix:
        lines.append(Text.assemble(("  fix  ", DIM), (err.fix, ACCENT)))
    lines.append(Text(f"  code {err.code} · exit {err.exit_code}", style=DIM))
    return Group(*lines)


def progress(message: str) -> None:
    """One progress line on stderr (never on stdout, so JSON stays clean)."""
    ui.err.print(Text.assemble(("· ", DIM), (message, DIM)))


# ------------------------------------------------------------------ widgets


def header(title: str, subtitle: str = "") -> Text:
    return Text.assemble(("▍", ACCENT), (title, "bold"), ("  " + subtitle if subtitle else "", DIM))


def mark(ok: bool | None) -> Text:
    if ok is None:
        return Text("–", style=DIM)
    return Text("●", style=OK) if ok else Text("✕", style=BAD)


def kv(rows: list[tuple[str, str | Text]]) -> Table:
    t = Table.grid(padding=(0, 2))
    t.add_column(style=DIM, no_wrap=True)
    t.add_column()
    for k, v in rows:
        t.add_row(k, v)
    return t


def table(columns: list[str], rows: list[list], *, title: str = "") -> Table:
    t = Table(
        box=box.SIMPLE_HEAD,
        show_edge=False,
        pad_edge=False,
        header_style=DIM,
        title=title or None,
        title_justify="left",
        title_style=f"bold {ACCENT}",
    )
    for c in columns:
        t.add_column(c, overflow="fold")
    for r in rows:
        t.add_row(*[c if isinstance(c, Text) else Text("" if c is None else str(c)) for c in r])
    return t


def next_block(steps: list[str]) -> Group:
    lines = [Text("next", style=f"bold {ACCENT}")]
    for s in steps:
        lines.append(Text.assemble(("  → ", ACCENT), (s, "bold")))
    return Group(Text(""), *lines)
