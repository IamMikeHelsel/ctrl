"""Lean 4 theorem registry and automated spec-manifest verification for ctrl.robotics.

Every public function in ``ctrl.robotics`` is decorated with ``@lean_theorem(...)`` linking it
to one or more kernel-checked theorems or definitions in ``lean/`` (across ``Research``,
``ControlsLean``, and ``RoboLean``). The ``verify_lean_bindings`` function audits every
registered Python symbol against the actual ``.lean`` files in the repository, checking:
1. The module file exists under ``lean/``.
2. Every referenced Lean theorem/lemma/def exists in that module.
3. The module contains zero forbidden proof escapes (``sorry``, ``admit``, ``native_decide``).
"""

from __future__ import annotations

import re
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path
from typing import Any, TypeVar

F = TypeVar("F", bound=Callable[..., Any])

FORBIDDEN_LEAN_TOKENS = ("sorry", "admit", "native_decide")


@dataclass(frozen=True)
class LeanBinding:
    """Metadata linking a Python callable to its formal Lean 4 specification."""

    py_qualname: str
    py_module: str
    lean_module: str
    lean_theorems: tuple[str, ...]
    domain: str
    summary: str

    def lean_rel_path(self) -> str:
        return "lean/" + self.lean_module.replace(".", "/") + ".lean"


LEAN_THEOREM_REGISTRY: list[LeanBinding] = []


def lean_theorem(
    module: str,
    theorems: str | tuple[str, ...] | list[str],
    *,
    domain: str,
    summary: str,
) -> Callable[[F], F]:
    """Decorator registering a Python function's machine-checked Lean 4 theorem provenance."""
    if isinstance(theorems, str):
        thm_tuple = (theorems,)
    else:
        thm_tuple = tuple(theorems)

    def decorator(fn: F) -> F:
        # Avoid duplicate registration from @overload stubs
        if getattr(fn, "__name__", "").startswith("_") or fn.__doc__ is None:
            return fn
        binding = LeanBinding(
            py_qualname=f"{fn.__module__}.{fn.__qualname__}",
            py_module=fn.__module__,
            lean_module=module,
            lean_theorems=thm_tuple,
            domain=domain,
            summary=summary,
        )
        if not any(b.py_qualname == binding.py_qualname for b in LEAN_THEOREM_REGISTRY):
            LEAN_THEOREM_REGISTRY.append(binding)
        fn.__lean_binding__ = binding  # type: ignore[attr-defined]
        return fn

    return decorator


def _strip_lean_comments_and_strings(text: str) -> str:
    """Remove block comments ``/- ... -/``, line comments ``-- ...``, and string literals."""
    out: list[str] = []
    i = 0
    n = len(text)
    depth = 0
    in_str = False
    while i < n:
        if depth == 0 and not in_str and text[i : i + 2] == "/-":
            depth = 1
            i += 2
            continue
        if depth > 0:
            if text[i : i + 2] == "/-":
                depth += 1
                i += 2
            elif text[i : i + 2] == "-/":
                depth -= 1
                i += 2
            else:
                i += 1
            continue
        if not in_str and text[i : i + 2] == "--":
            while i < n and text[i] != "\n":
                i += 1
            continue
        if text[i] == '"':
            in_str = not in_str
            i += 1
            continue
        if in_str and text[i] == "\\" and i + 1 < n:
            i += 2
            continue
        if not in_str:
            out.append(text[i])
        i += 1
    return "".join(out)


def audit_lean_file(path: Path) -> dict[str, Any]:
    """Inspect a single ``.lean`` file for declarations and forbidden tokens."""
    if not path.is_file():
        return {
            "exists": False,
            "declarations": set(),
            "forbidden_tokens": ["FILE_MISSING"],
            "lines": 0,
        }
    raw = path.read_text(encoding="utf-8")
    stripped = _strip_lean_comments_and_strings(raw)
    decl_pattern = re.compile(
        r"\b(?:theorem|lemma|def|noncomputable\s+def|abbrev|structure)\s+([^\s({:\[]+)"
    )
    decls = set(decl_pattern.findall(stripped))
    # Also include short suffixes when namespaced declarations like `Unicycle.arc_on_circle` appear
    short_decls = {d.split(".")[-1] for d in decls}
    all_decls = decls | short_decls

    forbidden: list[str] = []
    for tok in FORBIDDEN_LEAN_TOKENS:
        if re.search(rf"\b{re.escape(tok)}\b", stripped):
            forbidden.append(tok)

    return {
        "exists": True,
        "declarations": all_decls,
        "forbidden_tokens": forbidden,
        "lines": len(raw.splitlines()),
    }


def verify_lean_bindings(repo_root: Path | None = None) -> dict[str, Any]:
    """Verify all ``@lean_theorem`` bindings in ``LEAN_THEOREM_REGISTRY`` against ``lean/``."""
    if repo_root is None:
        repo_root = Path(__file__).resolve().parents[3]
    lean_root = repo_root / "lean"

    file_cache: dict[str, dict[str, Any]] = {}
    results: list[dict[str, Any]] = []
    missing_theorems: list[str] = []
    forbidden_hits: list[str] = []

    for binding in LEAN_THEOREM_REGISTRY:
        rel_path = binding.lean_rel_path()
        abs_path = repo_root / rel_path
        if rel_path not in file_cache:
            file_cache[rel_path] = audit_lean_file(abs_path)
        info = file_cache[rel_path]

        missing_in_binding = [
            thm for thm in binding.lean_theorems if thm not in info["declarations"]
        ]
        ok = (
            info["exists"]
            and not missing_in_binding
            and len(info["forbidden_tokens"]) == 0
        )
        if missing_in_binding:
            for thm in missing_in_binding:
                missing_theorems.append(f"{binding.py_qualname} -> {binding.lean_module}.{thm}")
        if info["forbidden_tokens"]:
            forbidden_hits.append(f"{rel_path}: {info['forbidden_tokens']}")

        results.append(
            {
                "py_qualname": binding.py_qualname,
                "domain": binding.domain,
                "lean_module": binding.lean_module,
                "lean_file": rel_path,
                "lean_theorems": list(binding.lean_theorems),
                "missing_theorems": missing_in_binding,
                "forbidden_tokens": info["forbidden_tokens"],
                "ok": ok,
                "summary": binding.summary,
            }
        )

    # Also scan all 53 modules in the unified Robotics library for completeness
    robotics_dirs = [
        lean_root / "Research",
        lean_root / "ControlsLean",
        lean_root / "RoboLean",
    ]
    all_robotics_files: list[Path] = []
    for d in robotics_dirs:
        if d.is_dir():
            all_robotics_files.extend(sorted(d.rglob("*.lean")))

    total_lines = 0
    total_decls = 0
    for f in all_robotics_files:
        rel = str(f.relative_to(repo_root))
        if rel not in file_cache:
            file_cache[rel] = audit_lean_file(f)
        finfo = file_cache[rel]
        total_lines += finfo["lines"]
        total_decls += len(finfo["declarations"])
        if finfo["forbidden_tokens"]:
            forbidden_hits.append(f"{rel}: {finfo['forbidden_tokens']}")

    return {
        "ok": len(missing_theorems) == 0 and len(forbidden_hits) == 0 and len(results) > 0,
        "registered_functions": len(results),
        "total_lean_theorems_bound": sum(len(b.lean_theorems) for b in LEAN_THEOREM_REGISTRY),
        "robotics_lean_modules": len(all_robotics_files),
        "robotics_lean_lines": total_lines,
        "robotics_lean_declarations": total_decls,
        "missing_theorems": missing_theorems,
        "forbidden_hits": sorted(set(forbidden_hits)),
        "bindings": results,
    }
