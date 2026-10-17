"""Checks 1-4 of docs/architecture.md for one problem. Called by check.sh; stdlib only.

Prints exactly one JSON object on stdout:
  {"nnn", "build": {"ok", "log"}, "tokens": {"ok", "hits"}, "axioms": {"ok", "axioms", ...},
   "binding": {"ok", "detail"}}
Exit 0 iff every check is ok, 4 if any check failed, 2 on bad usage.
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

LEAN_DIR = Path(__file__).resolve().parent.parent
REPO_DIR = LEAN_DIR.parent
LOG_LIMIT = 4000
MAX_HEARTBEATS = 400000
STANDARD_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
TIER_AXIOMS = {
    "default": STANDARD_AXIOMS,
    "reduceBool": STANDARD_AXIOMS + ["Lean.ofReduceBool"],
}
RESULT_MARKER = "CTRL_CHECK_JSON:"
ANSI = re.compile(r"\x1b\[[0-9;]*[A-Za-z]")

# (token label, regex) applied to source with comments and string literals blanked out.
FORBIDDEN = [
    ("sorry", re.compile(r"(?<![\w.'])sorry(?![\w'])")),
    ("admit", re.compile(r"(?<![\w.'])admit(?![\w'])")),
    ("axiom", re.compile(r"(?<![\w.'])axiom(?![\w'])")),
    ("opaque", re.compile(r"(?<![\w.'])opaque(?![\w'])")),
    ("implemented_by", re.compile(r"implemented_by")),
    ("extern", re.compile(r"@\[\s*extern\b|\bextern\s+\"")),
    ("native_decide", re.compile(r"native_decide")),
    ("decide +native", re.compile(r"\+\s*native\b|\bnative\s*:=\s*true")),
    ("Lean.ofReduceBool", re.compile(r"ofReduceBool|ofReduceNat")),
    ("set_option debug.", re.compile(r"\bset_option\s+debug\.")),
]
HEARTBEATS = re.compile(r"\bmaxHeartbeats\s+(\d+)")


def run(cmd: list[str], **kw) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=LEAN_DIR, capture_output=True, text=True, **kw)


def tail(text: str) -> str:
    text = ANSI.sub("", text)
    return text if len(text) <= LOG_LIMIT else "…" + text[-LOG_LIMIT:]


# --------------------------------------------------------------------------- tokens


def blank_comments_and_strings(src: str) -> str:
    """Replace comments (incl. nested /- -/ and docstrings) and string literals with spaces,
    keeping newlines so that line numbers survive."""
    out: list[str] = []
    i, n, depth = 0, len(src), 0
    in_str = False
    while i < n:
        c = src[i]
        two = src[i : i + 2]
        if depth:
            if two == "/-":
                depth += 1
                out.append("  ")
                i += 2
            elif two == "-/":
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif in_str:
            if c == "\\" and i + 1 < n:
                out.append("  " if src[i + 1] != "\n" else " \n")
                i += 2
                continue
            if c == '"':
                in_str = False
            out.append("\n" if c == "\n" else " ")
            i += 1
        elif two == "/-":
            depth = 1
            out.append("  ")
            i += 2
        elif two == "--":
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif c == '"' and not (i > 0 and src[i - 1] == "'"):  # skip the char literal '"'
            in_str = True
            out.append(" ")
            i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def solution_files(nnn: str) -> list[Path]:
    files = []
    main = LEAN_DIR / "ErdosLab" / f"Erdos{nnn}.lean"
    if main.exists():
        files.append(main)
    sub = LEAN_DIR / "ErdosLab" / f"Erdos{nnn}"
    if sub.is_dir():
        files.extend(sorted(sub.rglob("*.lean")))
    return files


def check_tokens(nnn: str) -> dict:
    hits = []
    files = solution_files(nnn)
    for path in files:
        raw = path.read_text(encoding="utf-8")
        raw_lines = raw.splitlines()
        code_lines = blank_comments_and_strings(raw).splitlines()
        rel = str(path.relative_to(REPO_DIR))
        for lineno, line in enumerate(code_lines, 1):
            text = raw_lines[lineno - 1].strip() if lineno <= len(raw_lines) else ""
            for label, rx in FORBIDDEN:
                if rx.search(line):
                    hits.append({"file": rel, "line": lineno, "token": label, "text": text})
            for m in HEARTBEATS.finditer(line):
                value = int(m.group(1))
                if value == 0 or value > MAX_HEARTBEATS:
                    hits.append(
                        {"file": rel, "line": lineno, "token": f"maxHeartbeats {value}",
                         "text": text}
                    )
    result = {"ok": bool(files) and not hits, "hits": hits}
    if not files:
        result["detail"] = f"no solution file lean/ErdosLab/Erdos{nnn}.lean"
    return result


# --------------------------------------------------------------------------- build


def check_build(nnn: str, fast: bool, olean_dir: Path) -> dict:
    challenge, solution = f"Challenge.Erdos{nnn}", f"ErdosLab.Erdos{nnn}"
    if not fast:
        p = run(["lake", "build", challenge, solution])
        return {"ok": p.returncode == 0, "log": tail(p.stdout + p.stderr)}
    p = run(["lake", "build", challenge])
    if p.returncode != 0:
        return {"ok": False, "log": tail(p.stdout + p.stderr)}
    out = olean_dir / "ErdosLab" / f"Erdos{nnn}.olean"
    out.parent.mkdir(parents=True, exist_ok=True)
    p = run(["lake", "env", "lean", "-o", str(out), f"ErdosLab/Erdos{nnn}.lean"])
    return {"ok": p.returncode == 0, "log": tail(p.stdout + p.stderr)}


# --------------------------------------------------------------------------- axioms + binding

PROBE = """import Lean
import ErdosLab.Erdos{nnn}
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let sol := `Challenge.Erdos{nnn}.solution
  let stmt := `Challenge.Erdos{nnn}.statement
  let modOf (n : Name) : String :=
    match env.getModuleIdxFor? n with
    | some i => toString (env.header.moduleNames[i.toNat]!)
    | none => "<current>"
  let kind : ConstantInfo → String
    | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
    | .opaqueInfo _ => "opaque" | _ => "other"
  let mut fields : List (String × Json) := []
  match env.find? sol with
  | none => fields := fields ++ [("solution_found", toJson false)]
  | some ci =>
    let axs ← collectAxioms sol
    fields := fields ++ [("solution_found", toJson true),
      ("solution_kind", toJson (kind ci)),
      ("solution_module", toJson (modOf sol)),
      ("solution_type_is_statement", toJson (ci.type == Expr.const stmt [])),
      ("solution_type", toJson (toString ci.type)),
      ("axioms", toJson (axs.map toString))]
  match env.find? stmt with
  | none => fields := fields ++ [("statement_found", toJson false)]
  | some ci =>
    fields := fields ++ [("statement_found", toJson true),
      ("statement_kind", toJson (kind ci)),
      ("statement_module", toJson (modOf stmt)),
      ("statement_is_prop", toJson (ci.type == Expr.sort Level.zero)),
      ("statement_levels", toJson ci.levelParams.length)]
  IO.println ("{marker}" ++ (Json.mkObj fields).compress)
"""


def axiom_tier(nnn: str) -> str:
    status = REPO_DIR / "work" / nnn / "status.json"
    try:
        return json.loads(status.read_text()).get("axiom_tier", "default") or "default"
    except (OSError, ValueError):
        return "default"


def probe(nnn: str, fast: bool, olean_dir: Path) -> tuple[dict | None, str]:
    with tempfile.TemporaryDirectory(prefix="ctrl-probe-") as tmp:
        path = Path(tmp) / f"Probe{nnn}.lean"
        path.write_text(PROBE.format(nnn=nnn, marker=RESULT_MARKER), encoding="utf-8")
        cmd = ["lake", "env", "lean", str(path)]
        if fast:
            # Let the freshly compiled solution olean shadow any stale one in .lake/build.
            cmd = ["lake", "env", "sh", "-c",
                   'LEAN_PATH="$0:$LEAN_PATH" exec lean "$1"', str(olean_dir), str(path)]
        p = run(cmd)
    out = p.stdout + p.stderr
    for line in p.stdout.splitlines():
        if line.startswith(RESULT_MARKER):
            try:
                return json.loads(line[len(RESULT_MARKER):]), out
            except ValueError:
                break
    return None, out


def check_axioms_binding(nnn: str, fast: bool, olean_dir: Path) -> tuple[dict, dict]:
    tier = axiom_tier(nnn)
    allowed = TIER_AXIOMS.get(tier)
    data, out = probe(nnn, fast, olean_dir)
    if data is None:
        msg = "probe failed: " + tail(out)
        return ({"ok": False, "axioms": [], "tier": tier, "detail": msg},
                {"ok": False, "detail": msg})
    if allowed is None:
        ax = {"ok": False, "axioms": data.get("axioms", []), "tier": tier,
              "detail": f"unknown axiom_tier {tier!r} in work/{nnn}/status.json"}
    elif not data.get("solution_found"):
        ax = {"ok": False, "axioms": [], "tier": tier,
              "detail": f"Challenge.Erdos{nnn}.solution not found"}
    else:
        axs = data["axioms"]
        bad = [a for a in axs if a not in allowed]
        ax = {"ok": not bad, "axioms": axs, "tier": tier, "allowed": allowed,
              "disallowed": bad}

    problems = []
    sol, stmt = f"Challenge.Erdos{nnn}.solution", f"Challenge.Erdos{nnn}.statement"
    if not data.get("statement_found"):
        problems.append(f"{stmt} not found")
    else:
        if data["statement_kind"] != "def":
            problems.append(f"{stmt} is a {data['statement_kind']}, expected def")
        if not data["statement_is_prop"]:
            problems.append(f"{stmt} does not have type Prop")
        if data["statement_levels"]:
            problems.append(f"{stmt} is universe polymorphic")
        if data["statement_module"] != f"Challenge.Erdos{nnn}":
            problems.append(f"{stmt} is declared in {data['statement_module']}, "
                            f"expected Challenge.Erdos{nnn}")
    if not data.get("solution_found"):
        problems.append(f"{sol} not found")
    else:
        if data["solution_kind"] != "theorem":
            problems.append(f"{sol} is a {data['solution_kind']}, expected theorem")
        if not data["solution_type_is_statement"]:
            problems.append(f"type of {sol} is not syntactically {stmt}: "
                            f"{data['solution_type'][:300]}")
        if data["solution_module"] != f"ErdosLab.Erdos{nnn}":
            problems.append(f"{sol} is declared in {data['solution_module']}, "
                            f"expected ErdosLab.Erdos{nnn}")
    detail = "; ".join(problems) if problems else f"{sol} : {stmt} (Expr.const), statement : Prop"
    return ax, {"ok": not problems, "detail": detail}


# --------------------------------------------------------------------------- main


def main(argv: list[str]) -> int:
    args = [a for a in argv if a != "--fast"]
    fast = "--fast" in argv
    if len(args) != 1 or not re.fullmatch(r"\d+", args[0]):
        print(json.dumps({"error": "usage: check.sh NNN [--fast]"}))
        return 2
    nnn = args[0]
    with tempfile.TemporaryDirectory(prefix="ctrl-olean-") as olean_tmp:
        olean_dir = Path(olean_tmp)
        tokens = check_tokens(nnn)
        build = check_build(nnn, fast, olean_dir)
        if build["ok"]:
            axioms, binding = check_axioms_binding(nnn, fast, olean_dir)
        else:
            skipped = "skipped: build failed"
            axioms = {"ok": False, "axioms": [], "tier": axiom_tier(nnn), "detail": skipped}
            binding = {"ok": False, "detail": skipped}
    result = {"nnn": nnn, "build": build, "tokens": tokens, "axioms": axioms,
              "binding": binding}
    print(json.dumps(result, ensure_ascii=False))
    return 0 if all(result[k]["ok"] for k in ("build", "tokens", "axioms", "binding")) else 4


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
