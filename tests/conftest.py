"""A throwaway ctrl repo per test, real FC fixtures, and a fake subprocess layer (no Lean, no SSH)."""

from __future__ import annotations

import json
import shutil
import subprocess
from pathlib import Path

import pytest

from erdos_lab import proc
from erdos_lab.cli import main

FIXTURES = Path(__file__).parent / "fixtures"
REAL = Path(__file__).resolve().parents[1]
PIN = "d9ce556af8ed4bdbd0ede2ed588d7cf4bb76cfdd"


class FakeProc:
    """Records every command; ``handlers[tool](cmd, kw)`` returns (rc, stdout, stderr)."""

    def __init__(self) -> None:
        self.calls: list[tuple[list[str], dict]] = []
        self.handlers: dict = {}

    def __call__(self, cmd, **kw):
        self.calls.append((list(cmd), kw))
        tool = Path(cmd[0]).name
        handler = self.handlers.get(tool)
        if handler is None:
            raise AssertionError(f"unexpected subprocess: {cmd}")
        rc, out, err = handler(list(cmd), kw)
        return subprocess.CompletedProcess(cmd, rc, out, err)

    def of(self, tool: str) -> list[tuple[list[str], dict]]:
        return [(c, k) for c, k in self.calls if Path(c[0]).name == tool]


@pytest.fixture
def repo(tmp_path, monkeypatch):
    root = tmp_path / "ctrl"
    (root / "erdos" / "Challenge").mkdir(parents=True)
    (root / "erdos" / "ErdosLab").mkdir(parents=True)
    (root / "erdos" / "scripts").mkdir(parents=True)
    (root / "work").mkdir()
    for name in ("lakefile.toml", "lean-toolchain", "Challenge.lean", "ErdosLab.lean"):
        shutil.copy(REAL / "erdos" / name, root / "erdos" / name)
    (root / "erdos" / "lake-manifest.json").write_text(
        json.dumps({"packages": [{"name": "formal_conjectures", "rev": PIN}]})
    )
    (root / "erdos" / "scripts" / "check.sh").write_text("#!/usr/bin/env bash\n")
    for k in ("CLAUDECODE", "CLAUDE_CODE", "ERDOS_AGENT", "ERDOS_JSON", "SPARK_SSH_HOST"):
        monkeypatch.delenv(k, raising=False)
    monkeypatch.setenv("ERDOS_ROOT", str(root))
    monkeypatch.setenv("ERDOS_FC_DIR", str(FIXTURES))
    monkeypatch.setenv("ERDOS_DATA_DIR", str(FIXTURES / "data"))
    monkeypatch.setenv("HOME", str(tmp_path / "home"))
    monkeypatch.chdir(root)
    return root


@pytest.fixture
def fake(monkeypatch):
    f = FakeProc()
    monkeypatch.setattr(proc, "run", f)
    return f


@pytest.fixture
def run(capsys):
    def _run(*argv) -> tuple[int, dict]:
        """Run ctrl with --json; return (exit code, envelope)."""
        code = 0
        try:
            main(["--json", *argv])
        except SystemExit as exc:
            code = exc.code or 0
        out = capsys.readouterr().out
        envelope = json.loads(out)  # exactly one JSON document on stdout, nothing else
        return code, envelope

    return _run


def check_report(**overrides) -> str:
    """A check.sh stdout line, all green unless overridden."""
    report = {
        "nnn": "196",
        "build": {"ok": True, "log": ""},
        "tokens": {"ok": True, "hits": []},
        "axioms": {"ok": True, "axioms": ["propext", "Classical.choice", "Quot.sound"]},
        "binding": {"ok": True, "detail": "solution : Challenge.Erdos196.statement"},
    }
    report.update(overrides)
    return json.dumps(report)
