"""Link Python callables to the Lean declarations they implement, and check the links.

``@lean_theorem(module, names)`` records which Lean declarations a function is written
against. ``verify_lean_bindings()`` checks that each module file exists under the repo root
and declares every named theorem/def. The link is by name: the Python is hand-written and
tested, not extracted from Lean.
"""

from __future__ import annotations

import re
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path
from typing import Any, TypeVar

F = TypeVar("F", bound=Callable[..., Any])

REPO_ROOT = Path(__file__).resolve().parents[3]


@dataclass(frozen=True)
class LeanBinding:
    py_qualname: str
    lean_module: str
    lean_names: tuple[str, ...]

    def lean_path(self, root: Path = REPO_ROOT) -> Path:
        return root / (self.lean_module.replace(".", "/") + ".lean")


LEAN_THEOREM_REGISTRY: list[LeanBinding] = []


def lean_theorem(module: str, names: str | tuple[str, ...]) -> Callable[[F], F]:
    """Record that the decorated function implements the named declarations of ``module``."""
    names_t = (names,) if isinstance(names, str) else tuple(names)

    def deco(fn: F) -> F:
        b = LeanBinding(f"{fn.__module__}.{fn.__qualname__}", module, names_t)
        if b not in LEAN_THEOREM_REGISTRY:
            LEAN_THEOREM_REGISTRY.append(b)
        fn.__lean_binding__ = b  # type: ignore[attr-defined]
        return fn

    return deco


_DECL = re.compile(r"^\s*(?:private\s+|noncomputable\s+)*(?:theorem|lemma|def)\s+(\S+)", re.M)


def lean_declarations(path: Path) -> set[str]:
    return set(_DECL.findall(path.read_text(encoding="utf-8")))


def verify_lean_bindings(root: Path = REPO_ROOT) -> list[str]:
    """Return a list of problems (empty means every binding resolves)."""
    problems: list[str] = []
    for b in LEAN_THEOREM_REGISTRY:
        path = b.lean_path(root)
        if not path.is_file():
            problems.append(f"{b.py_qualname}: missing {path}")
            continue
        decls = lean_declarations(path)
        problems += [
            f"{b.py_qualname}: {b.lean_module} has no declaration {n}"
            for n in b.lean_names
            if n not in decls
        ]
    return problems
