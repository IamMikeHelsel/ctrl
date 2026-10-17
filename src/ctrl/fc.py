"""Read theorem statements out of a Formal Conjectures file and write challenge files.

This is a small, careful scanner, not a Lean parser. It strips comments (string-aware), tracks
bracket depth to find the ``:=`` that ends a theorem signature, and tracks
``namespace``/``section``/``end`` so it knows which ``open`` lines are in scope. Statement text
is copied verbatim from the original file (only re-indented), so the challenge carries the
community-reviewed wording. Anything it can't vouch for becomes a warning for the human
reviewer, who has to approve the challenge anyway.
"""

from __future__ import annotations

import re
import textwrap
from dataclasses import dataclass, field

OPEN = "([{⟨⦃⟦"
CLOSE = ")]}⟩⦄⟧"

_MODS = r"(?:(?:private|protected|noncomputable|nonrec|unsafe|partial)\s+)*"
_ATTR = r"(?:@\[(?:[^\[\]]|\[[^\[\]]*\])*\]\s*)?"
_NAME = r"([^\s:({\[⦃⟨]+)"
DECL_RE = re.compile(rf"(?m)^{_ATTR}{_MODS}(theorem|lemma)\s+{_NAME}")
DEF_RE = re.compile(rf"(?m)^{_ATTR}{_MODS}(def|abbrev)\s+{_NAME}")
ATTR_RE = re.compile(r"@\[((?:[^\[\]]|\[[^\[\]]*\])*)\]")
SCOPE_RE = re.compile(
    r"(?m)^(namespace|section|end|open|variable|local\s+(?:notation|infix[lr]?|prefix|postfix|macro)|noncomputable\s+section|public\s+section|@\[[^\]]*\]\s*public\s+section)\b(.*)$"
)


@dataclass
class Theorem:
    name: str  # as written, e.g. erdos_895.variants.eighteen
    namespace: str  # e.g. Erdos895
    binders: str
    type: str  # verbatim (comments kept), original indentation
    category: str = ""
    opens: list[str] = field(default_factory=list)  # in scope at the declaration
    open_in: list[str] = field(default_factory=list)  # `open X in` right before it
    warnings: list[str] = field(default_factory=list)
    needs_answer: str = ""  # why the statement can't be stated yet (empty if fine)

    @property
    def full_name(self) -> str:
        return f"{self.namespace}.{self.name}" if self.namespace else self.name

    @property
    def statement(self) -> str:
        """The `Prop`, re-indented to start at column 0: ``∀ binders, type`` if there are binders."""
        body = _reflow(self.type)
        if self.binders:
            return f"∀ {_reflow(self.binders)},\n" + textwrap.indent(body, "  ")
        return body

    def to_dict(self) -> dict:
        return {
            "name": self.name,
            "full_name": self.full_name,
            "category": self.category,
            "needs_answer": self.needs_answer,
        }


def strip_comments(src: str) -> str:
    """Replace comments with spaces, keeping newlines, so offsets match the original."""
    out = list(src)
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        if c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            i = j + 1
        elif src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                out[k] = " "
            i = j
        elif src.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif src.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            for k in range(i, j):
                if out[k] != "\n":
                    out[k] = " "
            i = j
        else:
            i += 1
    return "".join(out)


def _find_assign(s: str, i: int) -> int:
    """Index of the first ``:=`` at bracket depth 0 from ``i`` (-1 if none)."""
    depth = 0
    n = len(s)
    while i < n:
        c = s[i]
        if c == '"':
            j = i + 1
            while j < n and s[j] != '"':
                j += 2 if s[j] == "\\" else 1
            i = j + 1
            continue
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        elif depth == 0 and s.startswith(":=", i):
            return i
        i += 1
    return -1


def _find_colon(s: str) -> int:
    depth = 0
    for i, c in enumerate(s):
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        elif c == ":" and depth == 0 and not s.startswith(":=", i):
            return i
    return -1


def _reflow(text: str) -> str:
    lines = text.rstrip().split("\n")
    first = lines[0].strip()
    rest = textwrap.dedent("\n".join(lines[1:])).rstrip() if len(lines) > 1 else ""
    if not first:
        return rest.strip("\n")
    if not rest:
        return first
    # continuation lines keep their indentation relative to each other, nested under `first`
    return first + "\n" + textwrap.indent(rest, "  ")


def _scope_at(clean: str, pos: int) -> tuple[list[str], list[str], list[str]]:
    """(namespace stack, opens in scope, warnings) at offset ``pos``."""
    stack: list[tuple[str, str, list[str]]] = [("file", "", [])]
    warnings: list[str] = []
    for m in SCOPE_RE.finditer(clean, 0, pos):
        kind, rest = m.group(1), m.group(2).strip()
        if kind == "namespace":
            stack.append(("namespace", rest.split()[0] if rest else "", []))
        elif kind.endswith("section"):
            stack.append(("section", rest.split()[0] if rest else "", []))
        elif kind == "end":
            if len(stack) > 1:
                stack.pop()
        elif kind == "open":
            if re.search(r"\bin$", rest):
                continue  # scoped to the next command only
            stack[-1][2].append(rest)
        elif kind == "variable":
            warnings.append(
                "the FC file declares `variable`s; check the statement doesn't depend on them"
            )
        else:
            warnings.append(
                f"the FC file declares `{kind}` notation; the challenge can't see local notation"
            )
    namespaces = [name for k, name, _ in stack if k == "namespace" and name]
    opens = [o for _, _, os_ in stack for o in os_]
    return namespaces, opens, sorted(set(warnings))


def _attr_before(clean: str, start: int) -> str:
    """The `@[...]` attribute attached to the declaration starting at ``start``."""
    seg = clean[max(0, start - 2000) : start]
    best = ""
    for m in ATTR_RE.finditer(seg):
        if not seg[m.end() :].strip() or re.fullmatch(r"\s*" + _MODS, seg[m.end() :]):
            best = m.group(1)
    return best


def _open_in_before(clean: str, start: int) -> list[str]:
    """`open X in` lines right above the declaration (docstrings are already blanked out)."""
    out: list[str] = []
    for line in reversed(clean[:start].split("\n")[:-1]):
        if not line.strip():
            continue
        m = re.fullmatch(r"open\s+(.+?)\s+in\s*", line)
        if not m:
            break
        out.insert(0, m.group(1))
    return out


def sorry_defs(src: str) -> list[str]:
    """Names of `def`/`abbrev`s whose body is ``sorry`` (FC's way of writing "answer unknown")."""
    clean = strip_comments(src)
    names = []
    for m in DEF_RE.finditer(clean):
        eq = _find_assign(clean, m.end())
        if eq >= 0 and re.match(r"\s*sorry\b", clean[eq + 2 :]):
            names.append(m.group(2))
    return names


def parse(src: str) -> list[Theorem]:
    clean = strip_comments(src)
    unknown = sorry_defs(src)
    out: list[Theorem] = []
    for m in DECL_RE.finditer(clean):
        name = m.group(2)
        start = m.start(1)
        sig_start = m.end()
        warnings: list[str] = []
        if clean.startswith(".{", sig_start):
            close = clean.find("}", sig_start)
            warnings.append(
                "the FC theorem is universe-polymorphic; check the statement's universes"
            )
            sig_start = close + 1
        eq = _find_assign(clean, sig_start)
        if eq < 0:
            continue
        sig_clean = clean[sig_start:eq]
        colon = _find_colon(sig_clean)
        if colon < 0:
            continue
        binders = src[sig_start : sig_start + colon].strip()
        type_ = src[sig_start + colon + 1 : eq]
        type_clean = sig_clean[colon + 1 :]
        namespaces, opens, scope_warnings = _scope_at(clean, start)
        am = ATTR_RE.search(clean, m.start(), start)
        cat = am.group(1) if am else _attr_before(clean, m.start())
        cm = re.search(r"\bcategory\s+([^,\]]+)", cat)
        needs = ""
        whole = sig_clean
        if re.search(r"\banswer\s*\(\s*sorry\s*\)", whole):
            needs = "the statement contains `answer(sorry)`"
        else:
            for d in unknown:
                if re.search(r"(?<![\w.'])(?:[\w']+\.)*" + re.escape(d) + r"(?![\w'])", whole):
                    needs = f"the statement uses `{d}`, which FC defines as `sorry`"
                    break
            else:
                if re.search(r"(?<![\w'])sorry(?![\w'])", type_clean):
                    needs = "the statement contains `sorry`"
        out.append(
            Theorem(
                name=name,
                namespace=".".join(namespaces),
                binders=binders,
                type=type_,
                category=cm.group(1).strip() if cm else "",
                opens=opens,
                open_in=_open_in_before(clean, m.start()),
                warnings=warnings + scope_warnings,
                needs_answer=needs,
            )
        )
    return out


def candidates(theorems: list[Theorem], nnn: str) -> list[Theorem]:
    """The theorems that state problem NNN (``erdos_NNN`` and its parts/variants)."""
    own = [t for t in theorems if re.fullmatch(rf"erdos_?{nnn}(\..+)?", t.name)]
    return own or theorems


def pick(theorems: list[Theorem], part: str) -> Theorem | None:
    for t in theorems:
        if part in (t.name, t.full_name):
            return t
    suffix = [t for t in theorems if t.name.endswith("." + part)]
    return suffix[0] if len(suffix) == 1 else None


# ------------------------------------------------------------------ writing


APPROVED_RE = re.compile(r"(?m)^-- approved-by:.*$")
PENDING = "-- approved-by: (pending)"


def part_label(name: str) -> str:
    """``erdos_834.parts.ii`` → ``part ii``; ``erdos_895.variants.eighteen`` → ``variant eighteen``."""
    m = re.search(r"\.(parts|variants)\.(.+)$", name)
    if not m:
        return ""
    return ("part " if m.group(1) == "parts" else "variant ") + m.group(2)


def challenge_text(nnn: str, thm: Theorem, pin: str) -> str:
    """The challenge file, in the shape verified by a real build (erdos/Challenge/Erdos834.lean).

    The `open` lines come BEFORE `namespace Challenge.ErdosNNN`: inside that namespace,
    `open ErdosNNN` resolves to `Challenge.ErdosNNN` and silently fails to open `_root_.ErdosNNN`.
    """
    ns_opens = []
    if thm.namespace:
        parts = thm.namespace.split(".")
        ns_opens = [".".join(parts[: i + 1]) for i in range(len(parts))]
    open_lines = [f"open {' '.join(ns_opens)}"] if ns_opens else []
    open_lines += [f"open {o}" for o in thm.opens]
    open_in = "".join(f"open {o} in\n" for o in thm.open_in)
    label = part_label(thm.name)
    title = f"Erdős Problem {nnn}" + (f" ({label})" if label else "")
    module = f"FormalConjectures.ErdosProblems.«{nnn}»"
    return (
        f"import {module}\n"
        "\n"
        "/-!\n"
        f"# Challenge: {title}\n"
        "\n"
        f"Statement copied verbatim from `{thm.full_name}` in\n"
        f"{module} (google-deepmind/formal-conjectures @ {pin[:7]}, Apache-2.0).\n"
        f"Source: https://www.erdosproblems.com/{nnn}\n"
        "-/\n"
        "\n"
        + "".join(line + "\n" for line in open_lines)
        + ("\n" if open_lines else "")
        + f"namespace Challenge.Erdos{nnn}\n"
        "\n"
        f"{open_in}"
        f"/-- statement copied from {module} `{thm.name}`\n"
        "(Apache-2.0) -/\n"
        "def statement : Prop :=\n" + textwrap.indent(thm.statement, "    ") + "\n"
        "\n"
        f"{PENDING}\n"
        "\n"
        f"end Challenge.Erdos{nnn}\n"
    )


def solution_text(nnn: str) -> str:
    return (
        f"import Challenge.Erdos{nnn}\n"
        "\n"
        f"namespace Challenge.Erdos{nnn}\n"
        "\n"
        "theorem solution : statement := by\n"
        "  sorry\n"
        "\n"
        f"end Challenge.Erdos{nnn}\n"
    )


def approval_line(text: str) -> str | None:
    m = APPROVED_RE.search(text)
    return m.group(0) if m else None


def is_approved_line(line: str | None) -> bool:
    return bool(line) and line.strip() != PENDING


def set_approval(text: str, line: str) -> str:
    if APPROVED_RE.search(text):
        return APPROVED_RE.sub(lambda _m: line, text, count=1)
    return text.rstrip("\n") + "\n" + line + "\n"


def add_import(root_text: str, module: str) -> str:
    """Add ``import module`` to a root file (after the last import, or after leading comments)."""
    line = f"import {module}"
    lines = root_text.splitlines()
    if line in (x.strip() for x in lines):
        return root_text
    last = max((i for i, x in enumerate(lines) if x.startswith("import ")), default=-1)
    if last < 0:
        last = 0
        while last < len(lines) and (not lines[last].strip() or lines[last].startswith("--")):
            last += 1
        last -= 1
    lines.insert(last + 1, line)
    return "\n".join(lines) + "\n"
