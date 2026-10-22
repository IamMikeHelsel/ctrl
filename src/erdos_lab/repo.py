"""Where things live in the repo. Everything ctrl knows is derived from these files."""

from __future__ import annotations

import json
import os
import re
from dataclasses import dataclass
from pathlib import Path

from erdos_lab.errors import CtrlError, usage

FC_REL = Path("FormalConjectures") / "ErdosProblems"


def _is_root(d: Path) -> bool:
    return (d / "erdos" / "lakefile.toml").is_file()


def find_root(start: Path | None = None) -> Path:
    """``ERDOS_ROOT``, else walk up from cwd, else the checkout this package was installed from."""
    env = os.environ.get("ERDOS_ROOT")
    if env:
        return Path(env).expanduser().resolve()
    here = Path(start or Path.cwd()).resolve()
    for d in [here, *here.parents]:
        if _is_root(d):
            return d
    pkg = Path(__file__).resolve().parents[2]
    if _is_root(pkg):
        return pkg
    raise CtrlError(
        "TOOL_MISSING",
        f"no Erdős lab (erdos/lakefile.toml) in {here} or its parents",
        hint="run erdos from inside the ctrl checkout, or set ERDOS_ROOT",
        fix="cd ~/Dev/ctrl",
    )


def nnn_of(value: str) -> str:
    v = str(value).strip()
    if not re.fullmatch(r"\d{1,5}", v):
        raise usage(f"not a problem number: {value!r}", hint="NNN is the erdosproblems.com number")
    return str(int(v))


@dataclass(frozen=True)
class Repo:
    root: Path

    @classmethod
    def find(cls) -> Repo:
        return cls(find_root())

    @property
    def lean(self) -> Path:
        return self.root / "erdos"

    @property
    def work(self) -> Path:
        return self.root / "work"

    def challenge(self, nnn: str) -> Path:
        return self.lean / "Challenge" / f"Erdos{nnn}.lean"

    def solution(self, nnn: str) -> Path:
        return self.lean / "ErdosLab" / f"Erdos{nnn}.lean"

    def workdir(self, nnn: str) -> Path:
        return self.work / nnn

    def status_file(self, nnn: str) -> Path:
        return self.workdir(nnn) / "status.json"

    def rel(self, p: Path) -> str:
        try:
            return str(p.relative_to(self.root))
        except ValueError:
            return str(p)

    def toolchain(self) -> str:
        f = self.lean / "lean-toolchain"
        return f.read_text().strip() if f.exists() else ""

    def fc_pin(self) -> str:
        """The Formal Conjectures commit from lake-manifest.json (falls back to lakefile.toml)."""
        manifest = self.lean / "lake-manifest.json"
        if manifest.exists():
            for pkg in json.loads(manifest.read_text()).get("packages", []):
                if pkg.get("name") == "formal_conjectures":
                    return pkg.get("rev") or pkg.get("inputRev") or ""
        lakefile = self.lean / "lakefile.toml"
        if lakefile.exists():
            m = re.search(
                r'formal_conjectures"[^\[]*?rev\s*=\s*"([0-9a-f]+)"', lakefile.read_text()
            )
            if m:
                return m.group(1)
        return ""

    def fc_file(self, nnn: str) -> Path | None:
        """The pinned FC statement file, falling back to the reference clone."""
        candidates = [
            self.lean / ".lake" / "packages" / "formal_conjectures" / FC_REL / f"{nnn}.lean",
        ]
        alt = os.environ.get("ERDOS_FC_DIR") or str(Path.home() / "Dev" / "formal-conjectures")
        candidates.append(Path(alt).expanduser() / FC_REL / f"{nnn}.lean")
        for c in candidates:
            if c.is_file():
                return c
        return None

    def problems(self) -> list[str]:
        if not self.work.is_dir():
            return []
        out = [d.name for d in self.work.iterdir() if (d / "status.json").is_file()]
        return sorted(out, key=lambda s: int(s) if s.isdigit() else 10**9)
