"""Environment checks for the Mac and (with --remote) the Spark. Each is ``{name, where, ok, detail}``."""

from __future__ import annotations

import json
from pathlib import Path

from ctrl import proc, spark
from ctrl.repo import Repo

ELAN_DIRS = ("~/.elan/bin",)


def toolchain_dir(toolchain: str) -> str:
    """elan's directory name for a toolchain: leanprover/lean4:v4.33.1 → leanprover--lean4---v4.33.1."""
    return toolchain.replace("/", "--", 1).replace(":", "---", 1)


def _check(name: str, ok: bool, detail: str, where: str = "mac") -> dict:
    return {"name": name, "where": where, "ok": bool(ok), "detail": detail}


def _version(path: str) -> str:
    try:
        cp = proc.run([path, "--version"], timeout=10)
    except Exception:  # noqa: BLE001 - a broken tool is reported, not raised
        return path
    return ((cp.stdout or cp.stderr or "").strip().splitlines() or [path])[0]


def local(repo: Repo) -> list[dict]:
    out = []
    elan = proc.which("elan", *ELAN_DIRS)
    out.append(_check("elan", elan, _version(elan) if elan else "not found (install elan)"))
    lake = proc.which("lake", *ELAN_DIRS)
    out.append(_check("lake", lake, lake or "not found (comes with elan)"))
    tc = repo.toolchain()
    tdir = Path.home() / ".elan" / "toolchains" / toolchain_dir(tc) if tc else None
    tc_ok = bool(tdir and (tdir / "bin" / "lean").exists())
    out.append(
        _check(
            "toolchain",
            tc_ok,
            tc
            if tc_ok
            else f"{tc or 'lean/lean-toolchain missing'} not installed (elan toolchain install {tc})",
        )
    )
    uv = proc.which("uv")
    out.append(_check("uv", uv, _version(uv) if uv else "not found (brew install uv)"))
    pkgs = repo.lean / ".lake" / "packages"
    missing = [p for p in ("mathlib", "formal_conjectures") if not (pkgs / p).is_dir()]
    out.append(
        _check(
            "lean packages",
            not missing,
            "mathlib, formal_conjectures"
            if not missing
            else f"missing {', '.join(missing)} (cd lean && lake exe cache get)",
        )
    )
    cache = pkgs / "mathlib" / ".lake" / "build" / "lib"
    out.append(
        _check(
            "lean cache",
            cache.is_dir(),
            "Mathlib oleans present"
            if cache.is_dir()
            else "no Mathlib build (cd lean && lake exe cache get)",
        )
    )
    pin = repo.fc_pin()
    head_file = pkgs / "formal_conjectures" / ".git" / "HEAD"
    head = head_file.read_text().strip() if head_file.is_file() else ""
    out.append(
        _check(
            "fc pin",
            bool(pin) and head == pin,
            f"formal_conjectures at {pin[:12]}"
            if head == pin
            else f"checked out {head[:12] or '?'}, manifest pins {pin[:12] or '?'} (cd lean && lake update)",
        )
    )
    for tool in ("ssh", "rsync"):
        p = proc.which(tool)
        out.append(_check(tool, p, p or "not found (needed for ctrl spark)"))
    return out


REMOTE_SCRIPT = r"""
# Non-login ssh shells lack ~/.local/bin and elan: use the repo copy's env.sh when it exists,
# and put the same dirs on PATH ourselves for a first run (before any `ctrl spark sync`).
export PATH="$HOME/.local/bin:$HOME/opt/bin:$HOME/.elan/bin:$PATH"
[ -f "$HOME/__REPO__/tools/spark/env.sh" ] && source "$HOME/__REPO__/tools/spark/env.sh" >/dev/null 2>&1
c() { printf '{"name":"%s","ok":%s,"detail":"%s"}\n' "$1" "$2" \
  "$(printf '%s' "$3" | tr -d '"\\' | tr '\n\t\r' '   ' | cut -c1-200)"; }
v() { command -v "$1" >/dev/null 2>&1; }
ver() { "$@" 2>&1 | head -1; }
tool() {  # tool NAME: on PATH or in ~/.local/bin (full path)
  if v "$1"; then command -v "$1"; elif [ -x "$HOME/.local/bin/$1" ]; then echo "$HOME/.local/bin/$1"; fi
}
if v elan; then c elan true "$(ver elan --version)"; else c elan false "not found"; fi
if v lake; then c lake true "$(command -v lake)"; else c lake false "not found"; fi
tc='__TOOLCHAIN__'; d="$HOME/.elan/toolchains/__TCDIR__"
if [ -x "$d/bin/lean" ]; then c toolchain true "$tc"; else c toolchain false "$tc not installed"; fi
p=$(tool uv); if [ -n "$p" ]; then c uv true "$(ver "$p" --version)"; else c uv false "not found"; fi
if [ -d "$HOME/__REPO__/lean/.lake/packages/mathlib" ]; then
  c "lean packages" true "~/__REPO__/lean/.lake/packages/mathlib"
else c "lean packages" false "no ~/__REPO__/lean/.lake/packages/mathlib (ctrl spark sync)"; fi
if [ -d "$HOME/__REPO__/lean/.lake/packages/mathlib/.lake/build/lib" ]; then
  c "lean cache" true "Mathlib oleans present"
else c "lean cache" false "no Mathlib build in ~/__REPO__/lean (ctrl spark sync)"; fi
if v kissat; then c kissat true "$(ver kissat --version)"; else c kissat false "not found"; fi
if v cadical; then c cadical true "$(ver cadical --version)"; else c cadical false "not found"; fi
if [ -x "$HOME/venvs/solve/bin/python" ]; then
  if out=$("$HOME/venvs/solve/bin/python" -c 'import pysat, ortools, cvxpy, networkx; print("pysat ortools cvxpy networkx")' 2>&1); then
    c "venvs/solve" true "$out"
  else c "venvs/solve" false "$(printf '%s' "$out" | tail -1)"; fi
else c "venvs/solve" false "~/venvs/solve missing"; fi
if v tmux; then c tmux true "$(ver tmux -V)"; else c tmux false "not found (prove/solve jobs run in tmux)"; fi
if v ollama; then
  c ollama true "$(ver ollama --version)"
  if ollama show leanstral >/dev/null 2>&1; then
    c leanstral true "ollama show leanstral ok"
  else c leanstral false "ollama show leanstral failed (bash tools/spark/build-leanstral.sh)"; fi
else c ollama false "not found"; c leanstral false "ollama not found"; fi
p=$(tool lean-lsp-mcp); if [ -n "$p" ]; then c lean-lsp-mcp true "$p"; else c lean-lsp-mcp false "not found (uv tool install lean-lsp-mcp)"; fi
p=$(tool claude); if [ -n "$p" ]; then c claude true "$(ver "$p" --version)"; else c claude false "not found"; fi
"""


def remote_script(repo: Repo) -> str:
    tc = repo.toolchain()
    return (
        REMOTE_SCRIPT.replace("__TOOLCHAIN__", tc)
        .replace("__TCDIR__", toolchain_dir(tc))
        .replace("__REPO__", spark.REMOTE_REPO)
    )


def remote(repo: Repo) -> list[dict]:
    """All Spark checks in one ssh call. Raises SPARK_UNREACHABLE if ssh itself fails."""
    cp = spark.ssh(remote_script(repo))
    out = [_check("ssh", True, spark.host(), "spark")]
    for line in (cp.stdout or "").splitlines():
        try:
            obj = json.loads(line)
        except json.JSONDecodeError:
            continue
        out.append(_check(obj.get("name", "?"), obj.get("ok"), obj.get("detail", ""), "spark"))
    return out
