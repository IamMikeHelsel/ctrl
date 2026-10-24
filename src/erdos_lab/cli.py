"""ctrl command line: communicative for people, predictable for agents (docs/erdos-lab/cli.md).

Global flags work anywhere on the line (before a ``--``): --json, --plain.
"""

from __future__ import annotations

import functools
import re
import sys
from datetime import date

import typer
from rich.console import Group
from rich.text import Text

from erdos_lab import __version__, check, fc, spark, state
from erdos_lab import doctor as doctor_mod
from erdos_lab import targets as targets_mod
from erdos_lab.errors import (
    EXIT_ERROR,
    EXIT_FAILED_CHECK,
    EXIT_NEEDS_HUMAN,
    CtrlError,
    from_exception,
    usage,
)
from erdos_lab.repo import Repo, nnn_of
from erdos_lab.ui import (
    ACCENT,
    DIM,
    configure,
    fail,
    finish,
    header,
    kv,
    mark,
    progress,
    table,
    ui,
)

try:  # typer >= 0.20 vendors click
    from typer._click.exceptions import NoArgsIsHelpError, UsageError
except ImportError:  # pragma: no cover
    from click.exceptions import NoArgsIsHelpError, UsageError

GLOBAL_FLAGS = {"--json", "--plain"}

app = typer.Typer(
    add_completion=False,
    no_args_is_help=True,
    rich_markup_mode="rich",
    context_settings={"help_option_names": ["-h", "--help"]},
    help="[bold]erdos[/] — machine-checked Lean proofs of Erdős problems, and the evidence that "
    "they prove the right statement.\n\nGlobal: [cyan]--json[/] (agents/CI) · [cyan]--plain[/]. "
    "Start with [cyan]erdos doctor[/] and [cyan]erdos targets[/]; ask [cyan]erdos status[/] any time.",
)
spark_app = typer.Typer(
    no_args_is_help=True, help="Run work on the Spark (sparky.local) through tools/spark/."
)
app.add_typer(spark_app, name="spark")


def command(name: str, target=app, **kwargs):
    """Register a command whose failures render as structured, fixable errors."""
    full = name if target is app else f"spark {name}"

    def deco(fn):
        @functools.wraps(fn)
        def wrapper(*args, **kw):
            ui.command = full
            try:
                return fn(*args, **kw)
            except (SystemExit, KeyboardInterrupt, typer.Exit):
                raise
            except Exception as exc:  # every failure gets the same treatment
                fail(from_exception(exc))

        return target.command(name, **kwargs)(wrapper)

    return deco


def version_cb(value: bool) -> None:
    if value:
        ui.command = "version"
        finish({"version": __version__}, lambda d: Text(f"erdos {d['version']}"))
        raise typer.Exit()


@app.callback()
def root(
    json_: bool = typer.Option(False, "--json", help="One JSON envelope on stdout."),
    plain: bool = typer.Option(False, "--plain", help="No color."),
    version: bool = typer.Option(
        False, "--version", callback=version_cb, is_eager=True, help="Print the version."
    ),
) -> None:
    """Global flags are handled in main(); these options exist for --help."""


# ======================================================================= doctor


@command("doctor")
def doctor(
    remote: bool = typer.Option(
        True, "--remote/--no-remote", help="Also check the Spark (one ssh call)."
    ),
) -> None:
    """Check elan/lake/toolchain, uv and the Lean cache here, and the Spark's setup."""
    repo = Repo.find()
    checks = doctor_mod.local(repo)
    err = None
    if remote:
        progress(f"checking the Spark at {spark.host()}")
        try:
            checks += doctor_mod.remote(repo)
        except CtrlError as e:
            if e.code != "SPARK_UNREACHABLE":
                raise
            checks.append(
                {"name": "ssh", "where": "spark", "ok": False, "detail": e.hint or e.message}
            )
            err = e
    bad = [c for c in checks if not c["ok"]]
    bad_local = [c for c in bad if c["where"] == "mac"]
    if bad_local or (bad and err is None):
        first = (bad_local or bad)[0]
        err = CtrlError(
            "TOOL_MISSING",
            f"{len(bad)} check(s) failed, first: {first['name']} on {first['where']}",
            hint=first["detail"],
            fix=_fix_from(first["detail"]),
            exit_code=EXIT_ERROR,
        )
    nxt = ["erdos targets --tab formalize --top 10", "erdos status"] if not bad else []
    if err is not None and err.fix:
        nxt = [err.fix]

    def render(d):
        rows = [[mark(c["ok"]), c["where"], c["name"], c["detail"]] for c in d["checks"]]
        return Group(
            header("doctor", spark.host() if remote else "local only"),
            table(["", "where", "check", "detail"], rows),
        )

    finish({"checks": checks}, render, next=nxt, error=err)


def _fix_from(detail: str) -> str:
    """Checks put their remedy in trailing parentheses; fall back to the machines doc."""
    m = re.search(r"\(([^()]+)\)\s*$", detail or "")
    return m.group(1) if m else "$PAGER docs/erdos-lab/machines.md"


# ======================================================================= targets


@command("targets")
def targets(
    tab: str = typer.Option("open", "--tab", help="open | formalize"),
    top: int = typer.Option(20, "--top", help="How many rows (0 = all)."),
    prize: bool = typer.Option(False, "--prize", help="Only problems with an Erdős prize."),
    max_difficulty: int = typer.Option(
        None, "--max-difficulty", help="open: difficulty_1to5 ≤ D; formalize: effort ≤ D."
    ),
    min_fit: int = typer.Option(
        None, "--min-fit", help="open: ai_lean_fit_1to5 ≥ F; formalize: priority ≥ F."
    ),
) -> None:
    """Ranked rows from the target CSVs (ERDOS_DATA_DIR, data/erdos, or Drive lean/erdos-data)."""
    repo = Repo.find()
    rows = targets_mod.load(repo, tab)
    picked = targets_mod.select(
        rows, tab, top=top, prize=prize, max_difficulty=max_difficulty, min_fit=min_fit
    )
    started = set(repo.problems())
    first_fc = next((r for r in picked if r["has_fc"] and str(r["erdos_no"]) not in started), None)
    nxt = [f"erdos new {first_fc['erdos_no']}"] if first_fc else []
    warnings = [] if picked else ["no rows match these filters"]

    def render(d):
        if tab == "open":
            cols = ["#", "prize", "diff", "fit", "score", "FC", "route", "summary"]
            body = [
                [
                    r["erdos_no"],
                    r["prize"],
                    r["difficulty_1to5"],
                    r["ai_lean_fit_1to5"],
                    r["tractability_score"],
                    "yes" if r["has_fc"] else "no",
                    r["route"],
                    _clip(r["summary"], 50),
                ]
                for r in d["rows"]
            ]
        else:
            cols = ["#", "prize", "prio", "effort", "status", "FC", "summary"]
            body = [
                [
                    r["erdos_no"],
                    r["prize"],
                    r["priority_1to5"],
                    r["formalization_effort_1to5"],
                    r["status"],
                    "yes" if r["has_fc"] else "no",
                    _clip(r["summary"], 64),
                ]
                for r in d["rows"]
            ]
        return table(cols, body, title=f"{tab} · {len(d['rows'])} of {d['total']}")

    finish({"tab": tab, "total": len(rows), "rows": picked}, render, next=nxt, warnings=warnings)


def _clip(s: str, n: int) -> str:
    s = s or ""
    return s if len(s) <= n else s[: n - 1] + "…"


# ======================================================================= new


@command("new")
def new(
    nnn: str = typer.Argument(..., help="Erdős problem number."),
    force: bool = typer.Option(False, "--force", help="Overwrite an unapproved draft."),
    part: str = typer.Option(None, "--part", help="Which FC theorem, if there are several."),
) -> None:
    """Draft erdos/Challenge/ErdosNNN.lean from Formal Conjectures, plus the solution skeleton."""
    repo = Repo.find()
    nnn = nnn_of(nnn)
    src_path = repo.fc_file(nnn)
    if src_path is None:
        raise CtrlError(
            "NO_FC_STATEMENT",
            f"Formal Conjectures has no file for Erdős problem {nnn}",
            hint="looked in erdos/.lake/packages/formal_conjectures and ~/Dev/formal-conjectures; "
            "the targets column FC says whether a statement exists",
            fix="erdos targets --tab formalize --top 10",
        )
    warnings: list[str] = []
    if "/.lake/packages/" not in str(src_path):
        warnings.append(f"read {src_path} (reference clone), not the pinned package")
    src = src_path.read_text(encoding="utf-8")
    theorems = fc.candidates(fc.parse(src), nnn)
    listing = [t.to_dict() for t in theorems]
    if not theorems:
        raise CtrlError(
            "NO_FC_STATEMENT",
            f"no theorem found in {src_path.name}",
            hint="the FC file has no `theorem` declarations erdos can read",
            fix=f"$EDITOR {src_path}",
        )
    if part:
        thm = fc.pick(theorems, part)
        if thm is None:
            err = usage(
                f"no FC theorem {part!r} for {nnn}",
                hint="choose one of: " + ", ".join(t.name for t in theorems),
                fix=f"erdos new {nnn} --part {theorems[0].name}",
            )
            finish({"nnn": nnn, "fc_theorems": listing}, _render_theorems, error=err)
    elif len(theorems) == 1:
        thm = theorems[0]
    else:
        err = usage(
            f"Formal Conjectures has {len(theorems)} theorems for {nnn}; pick one with --part",
            hint="; ".join(f"{t.name} ({t.category or '?'})" for t in theorems),
            fix=f"erdos new {nnn} --part {theorems[0].name}",
        )
        finish({"nnn": nnn, "fc_theorems": listing}, _render_theorems, error=err)
    if thm.needs_answer:
        err = CtrlError(
            "NEEDS_ANSWER",
            f"{thm.full_name}: {thm.needs_answer}",
            hint="FC leaves the answer open, but a challenge must state the actual answer "
            "(e.g. True/False or a value). A human fills it in.",
            fix=f"write erdos/Challenge/Erdos{nnn}.lean by hand with the answer, or pick another --part",
            exit_code=EXIT_NEEDS_HUMAN,
        )
        finish({"nnn": nnn, "fc_theorems": listing}, _render_theorems, error=err)

    chal, sol, wd = repo.challenge(nnn), repo.solution(nnn), repo.workdir(nnn)
    if chal.exists() and fc.is_approved_line(fc.approval_line(chal.read_text())):
        raise CtrlError(
            "EXISTS",
            f"{repo.rel(chal)} is approved; erdos will not rewrite it",
            hint="approved challenges are frozen (docs/erdos-lab/rules.md); changing one is a human decision",
            fix=f"git diff {repo.rel(chal)}",
            exit_code=EXIT_NEEDS_HUMAN,
        )
    existing = [p for p in (chal, sol, wd / "status.json") if p.exists()]
    if existing and not force:
        raise CtrlError(
            "EXISTS",
            f"{repo.rel(existing[0])} already exists",
            hint="erdos new only writes fresh drafts",
            fix=f"erdos new {nnn} --force" + (f" --part {part}" if part else ""),
        )
    if existing:
        warnings.append("overwrote " + ", ".join(repo.rel(p) for p in existing))
    pin = repo.fc_pin()
    warnings += thm.warnings
    chal.parent.mkdir(parents=True, exist_ok=True)
    sol.parent.mkdir(parents=True, exist_ok=True)
    chal.write_text(fc.challenge_text(nnn, thm, pin), encoding="utf-8")
    sol.write_text(fc.solution_text(nnn), encoding="utf-8")
    written = [chal, sol]
    for root_file, module in (
        (repo.lean / "Challenge.lean", f"Challenge.Erdos{nnn}"),
        (repo.lean / "ErdosLab.lean", f"ErdosLab.Erdos{nnn}"),
    ):
        old = root_file.read_text() if root_file.exists() else ""
        new_text = fc.add_import(old, module)
        if new_text != old:
            root_file.write_text(new_text)
            written.append(root_file)
    wd.mkdir(parents=True, exist_ok=True)
    today = date.today().isoformat()
    for name, text in (
        ("plan.md", _plan_md(nnn, thm, pin)),
        ("log.md", f"# Log: Erdős Problem {nnn}\n\n"),
    ):
        p = wd / name
        if not p.exists():
            p.write_text(text, encoding="utf-8")
            written.append(p)
    _log(repo, nnn, f"{today} `erdos new {nnn}`: drafted challenge from FC `{thm.full_name}`")
    status = {
        "nnn": nnn,
        "phase": "draft",
        "fc_theorem": thm.full_name,
        "fc_pin": pin,
        "axiom_tier": "default",
    }
    state.save(repo, nnn, status)
    written.append(wd / "status.json")
    data = {
        "nnn": nnn,
        "files": [repo.rel(p) for p in written],
        "fc_theorems": listing,
        "fc_theorem": thm.full_name,
        "fc_file": str(src_path),
        "fc_pin": pin,
        "statement": thm.statement,
    }

    def render(d):
        return Group(
            header(f"new {nnn}", d["fc_theorem"]),
            Text(d["statement"], style=ACCENT),
            kv([("wrote", "\n".join(d["files"]))]),
        )

    warnings.append(
        f"a human must compare {repo.rel(chal)} with erdosproblems.com/{nnn} before approving"
    )
    finish(data, render, next=[f"erdos approve {nnn} --by <name>"], warnings=warnings)


def _render_theorems(d):
    rows = [[t["name"], t["category"], t["needs_answer"] or "ok"] for t in d["fc_theorems"]]
    return table(["FC theorem", "category", "statement"], rows, title=f"Erdős {d['nnn']}")


def _plan_md(nnn: str, thm: fc.Theorem, pin: str) -> str:
    return f"""# Erdős Problem {nnn}

<https://www.erdosproblems.com/{nnn}> · Formal Conjectures `{thm.full_name}`
({thm.category or "uncategorized"}) at `{pin[:12]}` · challenge `erdos/Challenge/Erdos{nnn}.lean`

## Why
<!-- target-scout: five lines. Why this problem, why now, the expected route, the risk. -->

## Statement review
<!-- statement-drafter: compare the challenge with the source paper and erdosproblems.com/{nnn}.
Is it faithful? Vacuous? Off by one? Missing hypotheses? Then a human runs
`erdos approve {nnn} --by <name>`. -->

## Blueprint
<!-- proof-planner: lemma DAG. Each node stated in Lean (as sorry) and tagged
mathlib / elementary / search / hard. -->

## Log pointer
Attempts, failure reports and verifier reports go in [log.md](log.md).
"""


def _log(repo: Repo, nnn: str, line: str) -> None:
    p = repo.workdir(nnn) / "log.md"
    if p.exists():
        text = p.read_text()
        p.write_text(text + ("" if text.endswith("\n") else "\n") + f"- {line}\n")


# ======================================================================= approve


@command("approve")
def approve(
    nnn: str = typer.Argument(..., help="Erdős problem number."),
    by: str = typer.Option(None, "--by", help="Your name. Approval is a human act."),
) -> None:
    """Record `-- approved-by:` in the challenge and its sha256 in status.json."""
    repo = Repo.find()
    nnn = nnn_of(nnn)
    if not by or not by.strip():
        raise CtrlError(
            "NOT_APPROVED",
            "approve needs --by NAME",
            hint="approval is a human's signature after reviewing the statement; "
            "agents must not approve on their own",
            fix=f"erdos approve {nnn} --by <name>",
            exit_code=EXIT_NEEDS_HUMAN,
        )
    by = by.strip()
    if not re.fullmatch(r"[\w .@'-]{1,64}", by):
        raise usage(f"--by {by!r}: use a plain name", fix=f"erdos approve {nnn} --by <name>")
    chal = repo.challenge(nnn)
    if not chal.exists():
        raise usage(f"{repo.rel(chal)} does not exist", fix=f"erdos new {nnn}")
    if state.has_sorry(chal):
        raise CtrlError(
            "NEEDS_ANSWER",
            f"{repo.rel(chal)} still contains sorry",
            hint="a challenge must state the actual answer before it can be approved",
            fix=f"$EDITOR {repo.rel(chal)}",
            exit_code=EXIT_NEEDS_HUMAN,
        )
    st = state.load(repo, nnn) or {"nnn": nnn, "phase": "draft", "axiom_tier": "default"}
    before = state.approval(repo, nnn, st)
    warnings = []
    if before["ok"]:
        warnings.append(f"already approved ({before['detail']}); nothing changed")
        line = fc.approval_line(chal.read_text()) or ""
    else:
        if before["approved"]:
            warnings.append("the challenge changed after its last approval; re-approving")
        today = date.today().isoformat()
        line = f"-- approved-by: {by} {today}"
        chal.write_text(fc.set_approval(chal.read_text(), line), encoding="utf-8")
        st["challenge_sha256"] = state.sha256(chal)  # hash AFTER writing the line
        st["phase"] = "approved"
        st["approved_by"] = by
        st["approved_at"] = today
        st.pop("last_check", None)
        st.pop("last_spark_check", None)
        state.save(repo, nnn, st)
        _log(repo, nnn, f"{today} `erdos approve {nnn} --by {by}`: sha256 {st['challenge_sha256']}")
    data = {
        "nnn": nnn,
        "file": repo.rel(chal),
        "line": line,
        "hash": st["challenge_sha256"],
        "phase": st["phase"],
    }
    finish(
        data,
        lambda d: Group(header(f"approve {nnn}", d["line"]), kv([("sha256", d["hash"])])),
        next=[f"erdos check {nnn} --fast", f"erdos spark prove {nnn}"],
        warnings=warnings,
    )


# ======================================================================= check


def _render_results(d):
    def cell(r, k):
        return mark(r[k]["ok"])

    rows = [
        [r["nnn"], *(cell(r, k) for k, _ in check.CHECKS), ", ".join(r["failed"]) or "ok"]
        for r in d["results"]
    ]
    return table(["#", "build", "tokens", "axioms", "binding", "hash", "result"], rows)


@command("check")
def check_cmd(
    nnn: str = typer.Argument(None, help="Erdős problem number."),
    all_: bool = typer.Option(False, "--all", help="Every problem under work/."),
    fast: bool = typer.Option(False, "--fast", help="`lake env lean` on the solution only."),
) -> None:
    """Build, audit tokens and axioms, check the binding and the challenge hash."""
    repo = Repo.find()
    if bool(nnn) == bool(all_):
        raise usage("give one problem number or --all", fix="erdos check --all")
    nnns = [nnn_of(nnn)] if nnn else repo.problems()
    rows, warnings = _check_rows(repo, nnns, fast=fast, skip_missing=all_)
    err = check.error_for(rows)
    if err:
        nxt = [err.fix]
    elif fast:
        nxt = [f"erdos check {r['nnn']}" for r in rows]
    else:
        nxt = [f"erdos spark check {r['nnn']}" for r in rows]
    if all_ and not rows:
        warnings.append("no problems under work/")
        nxt = ["erdos status"]
    finish({"results": rows}, _render_results, next=nxt, warnings=warnings, error=err)


def _check_rows(
    repo: Repo, nnns: list[str], *, fast: bool, skip_missing: bool
) -> tuple[list[dict], list[str]]:
    warnings: list[str] = []
    rows: list[dict] = []
    for n in nnns:
        if not repo.solution(n).exists():
            if skip_missing:
                warnings.append(f"{n}: no erdos/ErdosLab/Erdos{n}.lean, skipped")
                continue
            raise usage(f"erdos/ErdosLab/Erdos{n}.lean does not exist", fix=f"erdos new {n}")
        progress(f"checking {n}{' (fast)' if fast else ''}: erdos/scripts/check.sh")
        row = check.result(repo, n, check.run_local(repo, n, fast))
        check.record(repo, n, row, fast=fast)
        rows.append(row)
    return rows, warnings


# ======================================================================= promote


@command("promote")
def promote(
    nnn: str = typer.Argument(..., help="Erdős problem number."),
    job: str = typer.Argument(..., help="A fetched job (work/NNN/candidates/JOB/)."),
) -> None:
    """Copy candidates/JOB/final.lean over the solution, then `erdos check NNN --fast`; undo on failure."""
    repo = Repo.find()
    nnn = nnn_of(nnn)
    job = spark.check_job_id(job)
    _require_approved(repo, nnn)
    cand_dir = repo.workdir(nnn) / "candidates" / job
    final = cand_dir / "final.lean"
    if not final.is_file():
        raise usage(f"{repo.rel(final)} does not exist", fix=f"erdos spark fetch {job}")
    diffs = sorted(cand_dir.glob("attempt-*/challenge.diff"))
    dirty = [d for d in diffs if d.read_text(errors="replace").strip()]
    if not diffs or dirty:
        raise CtrlError(
            "CHALLENGE_DRIFT",
            f"job {job} " + ("changed the challenge" if dirty else "has no challenge.diff"),
            hint=(
                "non-empty: " + ", ".join(repo.rel(d) for d in dirty)
                if dirty
                else "can't confirm the job left Challenge/ untouched (no attempt-*/challenge.diff)"
            ),
            fix=f"ls {repo.rel(cand_dir)}",
            exit_code=EXIT_FAILED_CHECK,
        )
    sol = repo.solution(nnn)
    previous = sol.read_bytes() if sol.exists() else None

    def restore() -> None:
        if previous is None:
            sol.unlink(missing_ok=True)
        else:
            sol.write_bytes(previous)

    sol.write_bytes(final.read_bytes())
    try:
        rows, warnings = _check_rows(repo, [nnn], fast=True, skip_missing=False)
    except BaseException:
        restore()
        raise
    err = check.error_for(rows)
    if err:
        restore()
        warnings.append(f"check failed; restored the previous {repo.rel(sol)}")
    else:
        _log(repo, nnn, f"{date.today().isoformat()} promoted `{job}` into {repo.rel(sol)}")
    data = {
        "nnn": nnn,
        "job": job,
        "candidate": repo.rel(final),
        "solution": repo.rel(sol),
        "promoted": err is None,
        "restored": err is not None,
        "results": rows,
    }
    nxt = [err.fix] if err else [f"erdos check {nnn}", f"git diff {repo.rel(sol)}"]
    finish(data, _render_results, next=nxt, warnings=warnings, error=err)


# ======================================================================= status


@command("status")
def status() -> None:
    """One row per work/NNN: phase and the next step."""
    repo = Repo.find()
    problems = [state.summary(repo, n) for n in repo.problems()]
    nxt = [p["next"][0] for p in problems if p["next"]]
    if not problems:
        nxt = ["erdos targets --tab formalize --top 10"]

    def render(d):
        if not d["problems"]:
            return Text("no problems under work/ yet", style=DIM)
        rows = [
            [
                p["nnn"],
                p["phase"],
                mark(p["hash_ok"]) if p["approved"] else Text("–", style=DIM),
                mark(p["last_check_ok"]),
                "; ".join(p["notes"]),
                " · ".join(p["next"]),
            ]
            for p in d["problems"]
        ]
        return table(["#", "phase", "approved", "check", "notes", "next"], rows)

    finish({"problems": problems}, render, next=nxt)


# ======================================================================= spark


@command("sync", spark_app)
def spark_sync(
    force: bool = typer.Option(
        False, "--force", help="Sync even while a prove job runs and the manifest changed."
    ),
) -> None:
    """rsync the repo to ~/lean-work/ctrl; `lake exe cache get` if the manifest changed."""
    repo = Repo.find()
    progress(f"rsync → {spark.host()}:~/{spark.REMOTE_REPO}")
    data = spark.sync(repo, force=force)

    def render(d):
        return kv(
            [
                ("host", d["host"]),
                ("changed", f"{len(d['changed'])} file(s)"),
                ("cache", "fetched" if d["cache_fetched"] else "unchanged"),
            ]
        )

    finish(data, render, next=["erdos spark check <NNN>", "erdos spark jobs"])


@command("check", spark_app)
def spark_check(nnn: str = typer.Argument(..., help="Erdős problem number.")) -> None:
    """sync, then tools/spark/check.sh NNN on the Spark."""
    repo = Repo.find()
    nnn = nnn_of(nnn)
    progress(f"rsync → {spark.host()}")
    synced = spark.sync(repo)
    progress(f"checking {nnn} on {spark.host()}: tools/spark/check.sh")
    cp = spark.run_script("check", [nnn])
    check.script_errors(cp, "tools/spark/check.sh")
    row = check.result(repo, nnn, check.parse_report(cp.stdout, cp.stderr, cp.returncode))
    check.record(repo, nnn, row, fast=False, where="spark")
    err = check.error_for([row])
    nxt = [err.fix] if err else ["erdos status"]
    finish({"results": [row], "sync": synced}, _render_results, next=nxt, error=err)


def _require_approved(repo: Repo, nnn: str) -> dict:
    st = state.load(repo, nnn)
    appr = state.approval(repo, nnn, st)
    if appr["ok"]:
        return st
    if appr["approved"]:
        raise CtrlError(
            "CHALLENGE_DRIFT",
            f"{nnn}: {appr['detail']}",
            hint="the statement must not change after approval",
            fix=f"git diff erdos/Challenge/Erdos{nnn}.lean",
            exit_code=EXIT_FAILED_CHECK,
        )
    raise CtrlError(
        "NOT_APPROVED",
        f"{nnn}: the challenge statement is not approved",
        hint="proving an unreviewed statement wastes the budget",
        fix=f"erdos approve {nnn} --by <name>",
        exit_code=EXIT_NEEDS_HUMAN,
    )


def _record_job(repo: Repo, nnn: str, job: str, kind: str, phase: str | None = None) -> None:
    st = state.load(repo, nnn) or {"nnn": nnn, "phase": "draft"}
    st.setdefault("jobs", []).append({"job": job, "kind": kind, "host": spark.host()})
    if phase and st.get("phase") == "approved":
        st["phase"] = phase
    state.save(repo, nnn, st)
    _log(repo, nnn, f"{date.today().isoformat()} spark {kind} job `{job}` started")


@command("prove", spark_app)
def spark_prove(
    nnn: str = typer.Argument(..., help="Erdős problem number."),
    minutes: int = typer.Option(None, "--minutes", help="Wall-clock budget."),
    model: str = typer.Option("leanstral", "--model", help="Ollama model on the Spark."),
    attempts: int = typer.Option(None, "--attempts", help="Attempt budget."),
    reasoning: str = typer.Option(None, "--reasoning", help="high | none (PROVE_REASONING)."),
    max_turns: int = typer.Option(None, "--max-turns", help="Per session (PROVE_MAX_TURNS)."),
) -> None:
    """sync, then tools/spark/prove.sh in tmux. Returns a job id."""
    repo = Repo.find()
    nnn = nnn_of(nnn)
    if reasoning is not None and reasoning not in ("high", "none"):
        raise usage(f"--reasoning {reasoning!r}: use high or none", fix=f"erdos spark prove {nnn}")
    env = {}
    if reasoning is not None:
        env["PROVE_REASONING"] = reasoning
    if max_turns is not None:
        if max_turns < 1:
            raise usage("--max-turns must be ≥ 1", fix=f"erdos spark prove {nnn}")
        env["PROVE_MAX_TURNS"] = str(max_turns)
    _require_approved(repo, nnn)
    progress(f"rsync → {spark.host()}")
    spark.sync(repo)
    args = [nnn, "--model", model]
    if minutes is not None:
        args += ["--minutes", str(minutes)]
    if attempts is not None:
        args += ["--attempts", str(attempts)]
    job = spark.start_job("prove", args, env)
    _record_job(repo, nnn, job, "prove", phase="proving")
    finish(
        {
            "job": job,
            "nnn": nnn,
            "model": model,
            "minutes": minutes,
            "attempts": attempts,
            "env": env,
        },
        lambda d: kv([("job", d["job"]), ("model", d["model"])]),
        next=[f"erdos spark log {job} -f", f"erdos spark fetch {job}"],
    )


@command(
    "solve",
    spark_app,
    context_settings={"allow_extra_args": True, "ignore_unknown_options": True},
)
def spark_solve(
    nnn: str = typer.Argument(..., help="Erdős problem number."),
    script: str = typer.Argument(..., help="Script under work/NNN/, e.g. search.py."),
    args: list[str] = typer.Argument(None, help="Arguments for the script (after --)."),
    timeout_min: int = typer.Option(
        None, "--timeout-min", help="Kill the run after N minutes (SOLVE_TIMEOUT_MIN)."
    ),
) -> None:
    """Run work/NNN/SCRIPT in ~/venvs/solve with the solvers on PATH, in tmux. Returns a job id."""
    repo = Repo.find()
    nnn = nnn_of(nnn)
    local = repo.workdir(nnn) / script
    if not local.is_file() or ".." in script.split("/"):
        raise usage(f"work/{nnn}/{script} does not exist", fix=f"ls work/{nnn}")
    progress(f"rsync → {spark.host()}")
    spark.sync(repo)
    env = {"SOLVE_TIMEOUT_MIN": str(timeout_min)} if timeout_min is not None else {}
    job = spark.start_job("solve", [nnn, script, *(args or [])], env)
    _record_job(repo, nnn, job, "solve")
    finish(
        {"job": job, "nnn": nnn, "script": script, "args": list(args or []), "env": env},
        lambda d: kv([("job", d["job"]), ("script", d["script"])]),
        next=[f"erdos spark log {job} -f", f"erdos spark fetch {job}"],
    )


@command("jobs", spark_app)
def spark_jobs() -> None:
    """List jobs in ~/lean-work/jobs on the Spark."""
    rows = spark.jobs()
    running = [r for r in rows if r.get("status") in spark.RUNNING]
    done = [r for r in rows if r.get("status") not in spark.RUNNING]
    nxt = [f"erdos spark log {r['job']} -f" for r in running[:1]]
    nxt += [f"erdos spark fetch {r['job']}" for r in done[:1]]

    def render(d):
        if not d["jobs"]:
            return Text("no jobs", style=DIM)
        body = [
            [
                r["job"],
                r.get("nnn", ""),
                r.get("kind", ""),
                r.get("status", ""),
                r.get("started", ""),
                r.get("elapsed_s", ""),
            ]
            for r in d["jobs"]
        ]
        return table(["job", "#", "kind", "status", "started", "elapsed s"], body)

    finish({"jobs": rows}, render, next=nxt)


@command("log", spark_app)
def spark_log(
    job: str = typer.Argument(..., help="Job id (erdos spark jobs)."),
    follow: bool = typer.Option(False, "-f", "--follow", help="Keep streaming."),
    lines: int = typer.Option(200, "-n", "--lines", help="Lines from the end."),
) -> None:
    """Tail a job's log.txt (tools/spark/log.sh; -f returns when the job ends)."""
    job = spark.check_job_id(job)
    if follow and ui.json:
        raise usage("-f streams raw text; drop --json", fix=f"erdos spark log {job} -f")
    cp = spark.log(job, lines, follow)
    if follow:
        finish({"job": job}, None, next=[f"erdos spark fetch {job}"])
        return
    finish(
        {"job": job, "log": cp.stdout or ""},
        lambda d: Text(d["log"].rstrip("\n")),
        next=[f"erdos spark log {job} -f", f"erdos spark fetch {job}"],
    )


@command("fetch", spark_app)
def spark_fetch(job: str = typer.Argument(..., help="Job id (erdos spark jobs).")) -> None:
    """Pull a job's outputs/ into work/NNN/candidates/JOB/ (never into erdos/)."""
    repo = Repo.find()
    job = spark.check_job_id(job)
    meta = spark.meta(job)
    if "nnn" not in meta:
        raise CtrlError(
            "REMOTE_FAILED", f"meta.json for job {job} has no nnn", fix=f"erdos spark log {job}"
        )
    nnn = nnn_of(str(meta["nnn"]))
    dest = repo.workdir(nnn) / "candidates" / job
    progress(f"rsync {spark.host()}:~/{spark.REMOTE_JOBS}/{job}/outputs/ → {repo.rel(dest)}")
    files = spark.fetch(job, dest)
    _log(repo, nnn, f"{date.today().isoformat()} fetched job `{job}` → {repo.rel(dest)}/")
    final = dest / "final.lean"
    candidate = repo.rel(final) if final.is_file() else None
    data = {
        "job": job,
        "nnn": nnn,
        "dest": repo.rel(dest),
        "files": files,
        "candidate": candidate,
        "meta": meta,
    }
    rows = [("job", job), ("status", str(meta.get("status", "?"))), ("into", data["dest"])]
    rows += [("files", str(len(files))), ("candidate", candidate or "none (no final.lean)")]
    warnings = [
        "candidates are untrusted: `erdos promote` copies final.lean into erdos/ErdosLab only if "
        "the job left Challenge/ untouched, then runs erdos check --fast and undoes a failure"
    ]
    nxt = [f"erdos promote {nnn} {job}", f"erdos check {nnn} --fast"] if candidate else []
    if meta.get("status") in spark.RUNNING:
        warnings.append(f"job {job} is still {meta.get('status')}; fetch again when it ends")
        nxt = [f"erdos spark log {job} -f"] + nxt
    finish(data, lambda d: kv(rows), next=nxt or [f"ls {data['dest']}"], warnings=warnings)


# ======================================================================= main


def _split_flags(argv: list[str]) -> tuple[set[str], list[str]]:
    if "--" in argv:
        i = argv.index("--")
        head, tail = argv[:i], argv[i:]
    else:
        head, tail = argv, []
    flags = {a for a in head if a in GLOBAL_FLAGS}
    return flags, [a for a in head if a not in GLOBAL_FLAGS] + tail


def main(argv: list[str] | None = None) -> None:
    """Entry point. Global flags are accepted anywhere on the line."""
    argv = list(sys.argv[1:] if argv is None else argv)
    flags, rest = _split_flags(argv)
    configure(json_mode="--json" in flags, plain="--plain" in flags)
    words = [a for a in rest if not a.startswith("-")][:2]
    ui.command = " ".join(words if words[:1] == ["spark"] else words[:1])
    try:
        app(args=rest, prog_name="erdos", standalone_mode=False)
    except NoArgsIsHelpError:  # typer already printed the help
        raise SystemExit(0) from None
    except UsageError as exc:
        fail(usage(exc.format_message(), fix="erdos --help"))
    except typer.Abort:
        raise SystemExit(130) from None
    except typer.Exit as exc:
        raise SystemExit(exc.exit_code) from None
    except CtrlError as exc:
        fail(exc)
    except KeyboardInterrupt:
        ui.err.print(Text("\n  stopped", style=DIM))
        raise SystemExit(130) from None


if __name__ == "__main__":  # pragma: no cover
    main()
