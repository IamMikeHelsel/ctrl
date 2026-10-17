"""The CLI is an API for agents: JSON envelopes, exit codes and error codes are contracts.

Ordered by how likely a test is to catch a real bug: statement binding and audit first, then
the CLI contract, then plumbing (docs/erdos-lab/cli.md, docs/erdos-lab/rules.md).
"""

from __future__ import annotations

import hashlib
import json

import pytest
from conftest import PIN, check_report

ENVELOPE_KEYS = {"ok", "command", "data", "warnings", "next", "error"}


def sha(path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def status(repo, nnn="196") -> dict:
    return json.loads((repo / "work" / nnn / "status.json").read_text())


def checksh(fake, *, rc=0, out=None, err=""):
    fake.handlers["bash"] = lambda cmd, kw: (rc, check_report() if out is None else out, err)


def approved(run, nnn="196"):
    assert run("new", nnn)[0] == 0
    assert run("approve", nnn, "--by", "mike")[0] == 0


# ---------------------------------------------------------------- check: binding, audit, hash


def test_check_passes_only_when_approved_and_all_green(repo, run, fake):
    checksh(fake)
    run("new", "196")
    code, env = run("check", "196")
    assert code == 3 and env["error"]["code"] == "NOT_APPROVED"
    assert env["data"]["results"][0]["failed"] == ["NOT_APPROVED"]
    assert env["next"] == ["ctrl approve 196 --by <name>"]

    run("approve", "196", "--by", "mike")
    code, env = run("check", "196")
    assert code == 0 and env["ok"] and env["error"] is None
    [row] = env["data"]["results"]
    assert set(row) >= {"nnn", "build", "tokens", "axioms", "binding", "hash"}
    assert all(row[k]["ok"] for k in ("build", "tokens", "axioms", "binding", "hash"))
    assert env["next"] == ["ctrl spark check 196"]
    cmd, kw = fake.of("bash")[-1]
    assert cmd == ["bash", "scripts/check.sh", "196"] and kw["cwd"] == repo / "erdos"
    st = status(repo)
    assert st["phase"] == "checked" and st["last_check"]["ok"] is True
    assert st["last_check"]["solution_sha256"] == sha(repo / "erdos/ErdosLab/Erdos196.lean")


@pytest.mark.parametrize(
    "key,payload,code",
    [
        ("build", {"ok": False, "log": "error: unknown identifier 'foo'"}, "LEAN_BUILD_FAILED"),
        ("tokens", {"ok": False, "hits": ["ErdosLab/Erdos196.lean:6: sorry"]}, "FORBIDDEN_TOKEN"),
        ("axioms", {"ok": False, "axioms": ["sorryAx"]}, "NONSTANDARD_AXIOM"),
        ("binding", {"ok": False, "detail": "solution : True"}, "BINDING_MISMATCH"),
    ],
)
def test_each_failed_check_maps_to_its_code_and_exit_4(repo, run, fake, key, payload, code):
    approved(run)
    checksh(fake, rc=4, out=check_report(**{key: payload}))
    rc, env = run("check", "196", "--fast")
    assert rc == 4 and env["error"]["code"] == code and not env["ok"]
    assert env["data"]["results"][0]["failed"] == [code]
    assert fake.of("bash")[-1][0] == ["bash", "scripts/check.sh", "196", "--fast"]
    assert status(repo)["phase"] == "proving"


def test_editing_an_approved_challenge_is_drift(repo, run, fake):
    approved(run)
    checksh(fake)
    chal = repo / "erdos/Challenge/Erdos196.lean"
    chal.write_text(chal.read_text().replace("HasMonotoneAP f 4", "HasMonotoneAP f 3"))
    code, env = run("check", "196")
    assert code == 4 and env["error"]["code"] == "CHALLENGE_DRIFT"
    assert env["data"]["results"][0]["hash"]["approved"] is True
    code, env = run("status")
    assert "changed after approval" in env["data"]["problems"][0]["notes"][0]
    code, env = run("spark", "prove", "196")
    assert code == 4 and env["error"]["code"] == "CHALLENGE_DRIFT"


def test_garbage_from_check_sh_is_a_failed_build(repo, run, fake):
    approved(run)
    checksh(fake, rc=4, out="", err="Segmentation fault")
    code, env = run("check", "196")
    assert code == 4 and env["error"]["code"] == "LEAN_BUILD_FAILED"
    assert "Segmentation fault" in env["data"]["results"][0]["build"]["log"]


def test_check_sh_exit_1_means_lake_missing(repo, run, fake):
    approved(run)
    checksh(fake, rc=1, out='{"error": "lake not found on PATH (install elan)"}')
    code, env = run("check", "196")
    assert code == 1 and env["error"]["code"] == "TOOL_MISSING"
    assert "lake not found" in env["error"]["message"]


def test_extra_axiom_keys_pass_through(repo, run, fake):
    approved(run)
    axioms = {"ok": True, "axioms": ["propext"], "tier": "default", "allowed": [], "disallowed": []}
    checksh(fake, out=check_report(axioms=axioms))
    code, env = run("check", "196")
    assert code == 0 and env["data"]["results"][0]["axioms"]["tier"] == "default"


def test_missing_check_fields_fail_closed(repo, run, fake):
    approved(run)
    checksh(fake, out=json.dumps({"nnn": "196", "build": {"ok": True, "log": ""}}))
    code, env = run("check", "196")
    assert code == 4 and env["error"]["code"] == "FORBIDDEN_TOKEN"
    assert set(env["data"]["results"][0]["failed"]) == {
        "FORBIDDEN_TOKEN",
        "NONSTANDARD_AXIOM",
        "BINDING_MISMATCH",
    }


def test_check_all_aggregates_and_failure_beats_unapproved(repo, run, fake):
    approved(run, "196")
    run("new", "834", "--part", "parts.ii")

    def handler(cmd, kw):
        nnn = cmd[2]
        if nnn == "196":
            return 4, check_report(axioms={"ok": False, "axioms": ["Lean.ofReduceBool"]}), ""
        return 0, check_report(nnn=nnn), ""

    fake.handlers["bash"] = handler
    code, env = run("check", "--all")
    assert [r["nnn"] for r in env["data"]["results"]] == ["196", "834"]
    assert code == 4 and env["error"]["code"] == "NONSTANDARD_AXIOM"
    assert env["data"]["results"][1]["failed"] == ["NOT_APPROVED"]


def test_check_usage(repo, run, fake):
    code, env = run("check")
    assert code == 2 and env["error"]["code"] == "BAD_USAGE"
    code, env = run("check", "196")
    assert code == 2 and env["error"]["fix"] == "ctrl new 196"


# ---------------------------------------------------------------- new / approve


def test_new_writes_challenge_solution_work_and_imports(repo, run):
    code, env = run("new", "196")
    assert code == 0 and env["command"] == "new"
    d = env["data"]
    assert d["fc_theorem"] == "Erdos196.erdos_196" and d["fc_pin"] == PIN
    assert [t["name"] for t in d["fc_theorems"]] == ["erdos_196"]
    assert set(d["files"]) >= {
        "erdos/Challenge/Erdos196.lean",
        "erdos/ErdosLab/Erdos196.lean",
        "erdos/Challenge.lean",
        "erdos/ErdosLab.lean",
        "work/196/plan.md",
        "work/196/log.md",
        "work/196/status.json",
    }
    chal = (repo / "erdos/Challenge/Erdos196.lean").read_text()
    assert chal.startswith("import FormalConjectures.ErdosProblems.«196»\n")
    assert f"@ {PIN[:7]}, Apache-2.0" in chal and "\n-- approved-by: (pending)\n" in chal
    assert "import Challenge.Erdos196" in (repo / "erdos/Challenge.lean").read_text()
    assert "import ErdosLab.Erdos196" in (repo / "erdos/ErdosLab.lean").read_text()
    plan = (repo / "work/196/plan.md").read_text()
    for section in ("## Why", "## Statement review", "## Blueprint", "## Log pointer"):
        assert section in plan
    assert status(repo) == {
        "nnn": "196",
        "phase": "draft",
        "fc_theorem": "Erdos196.erdos_196",
        "fc_pin": PIN,
        "axiom_tier": "default",
    }
    assert env["next"] == ["ctrl approve 196 --by <name>"]

    code, env = run("new", "196")
    assert code == 1 and env["error"]["code"] == "EXISTS"
    assert env["error"]["fix"] == "ctrl new 196 --force"
    code, env = run("new", "196", "--force")
    assert code == 0
    assert (repo / "erdos/Challenge.lean").read_text().count("import Challenge.Erdos196") == 1


def test_new_with_several_theorems_needs_part(repo, run):
    code, env = run("new", "895")
    assert code == 2 and env["error"]["code"] == "BAD_USAGE"
    assert env["error"]["fix"] == "ctrl new 895 --part erdos_895"
    assert len(env["data"]["fc_theorems"]) == 3
    assert not (repo / "erdos/Challenge/Erdos895.lean").exists()
    code, env = run("new", "895", "--part", "eighteen")
    assert code == 0 and env["data"]["fc_theorem"] == "Erdos895.erdos_895.variants.eighteen"
    chal = (repo / "erdos/Challenge/Erdos895.lean").read_text()
    assert "open Erdos895\nopen Filter\n" in chal
    assert "∀ (n : ℕ) (hn : 18 ≤ n)" in chal
    code, env = run("new", "834", "--part", "nope")
    assert code == 2 and env["error"]["code"] == "BAD_USAGE"


def test_new_refuses_unknown_answers_and_missing_files(repo, run):
    code, env = run("new", "1157")
    assert code == 3 and env["error"]["code"] == "NEEDS_ANSWER"
    assert not (repo / "erdos/Challenge/Erdos1157.lean").exists()
    code, env = run("new", "1074", "--part", "parts.ii")
    assert code == 3 and env["error"]["code"] == "NEEDS_ANSWER"
    code, env = run("new", "1074", "--part", "parts.i")
    assert code == 0
    code, env = run("new", "4242")
    assert code == 1 and env["error"]["code"] == "NO_FC_STATEMENT"
    code, env = run("new", "12ab")
    assert code == 2 and env["error"]["code"] == "BAD_USAGE"


def test_approve_records_line_then_hash(repo, run):
    run("new", "196")
    code, env = run("approve", "196")
    assert code == 3 and env["error"]["code"] == "NOT_APPROVED"
    assert env["error"]["fix"] == "ctrl approve 196 --by <name>"

    code, env = run("approve", "196", "--by", "mike")
    assert code == 0
    chal = repo / "erdos/Challenge/Erdos196.lean"
    text = chal.read_text()
    assert "(pending)" not in text
    assert [x for x in text.splitlines() if x.startswith("-- approved-by:")][0].startswith(
        "-- approved-by: mike 20"
    )
    assert env["data"]["hash"] == sha(chal) == status(repo)["challenge_sha256"]
    assert status(repo)["phase"] == "approved"
    assert env["next"][0] == "ctrl check 196 --fast"

    code, env = run("approve", "196", "--by", "mike")  # idempotent
    assert code == 0 and env["data"]["hash"] == sha(chal) and env["warnings"]

    code, env = run("new", "196", "--force")  # approved challenges are frozen
    assert code == 3 and env["error"]["code"] == "EXISTS"


def test_approve_refuses_a_challenge_with_sorry(repo, run):
    run("new", "196")
    chal = repo / "erdos/Challenge/Erdos196.lean"
    chal.write_text(chal.read_text().replace("HasMonotoneAP f 4", "HasMonotoneAP f sorry"))
    code, env = run("approve", "196", "--by", "mike")
    assert code == 3 and env["error"]["code"] == "NEEDS_ANSWER"


# ---------------------------------------------------------------- envelope, status, targets


def test_envelope_shape_is_stable(repo, run):
    for argv in (("status",), ("targets", "--top", "1"), ("new", "4242"), ("bogus",)):
        code, env = run(*argv)
        assert set(env) == ENVELOPE_KEYS, argv
        assert isinstance(env["warnings"], list) and isinstance(env["next"], list)
        assert all(isinstance(s, str) for s in env["next"])
        if env["error"] is not None:
            assert set(env["error"]) == {"code", "message", "hint", "fix"}
            assert env["ok"] is False and code != 0
    code, env = run("bogus")
    assert code == 2 and env["error"]["code"] == "BAD_USAGE"


def test_status_derives_next_steps_from_files(repo, run, fake):
    code, env = run("status")
    assert code == 0 and env["data"]["problems"] == []
    assert env["next"] == ["ctrl targets --tab formalize --top 10"]

    run("new", "196")
    code, env = run("status")
    [p] = env["data"]["problems"]
    assert p["phase"] == "draft" and p["next"] == ["ctrl approve 196 --by <name>"]

    run("approve", "196", "--by", "mike")
    [p] = run("status")[1]["data"]["problems"]
    assert p["phase"] == "approved" and p["next"][0] == "ctrl spark prove 196"

    sol = repo / "erdos/ErdosLab/Erdos196.lean"
    sol.write_text(sol.read_text().replace("sorry", "exact proof_of_196"))
    [p] = run("status")[1]["data"]["problems"]
    assert p["next"] == ["ctrl check 196"] and "never checked" in p["notes"]

    checksh(fake)
    run("check", "196")
    [p] = run("status")[1]["data"]["problems"]
    assert p["phase"] == "checked" and p["next"] == ["ctrl spark check 196"]

    sol.write_text(sol.read_text() + "\n-- golfed\n")
    [p] = run("status")[1]["data"]["problems"]
    assert p["stale"] and p["next"] == ["ctrl check 196"]


def test_targets_filter_and_sort(repo, run):
    code, env = run("targets", "--tab", "formalize", "--max-difficulty", "1", "--top", "0")
    rows = env["data"]["rows"]
    assert code == 0 and rows and all(r["formalization_effort_1to5"] <= 1 for r in rows)
    prios = [r["priority_1to5"] for r in rows]
    assert prios == sorted(prios, reverse=True)

    code, env = run("targets", "--tab", "formalize", "--top", "3")
    assert [r["erdos_no"] for r in env["data"]["rows"]] == [834, 895, 346]
    assert env["next"] == ["ctrl new 834"]

    code, env = run("targets", "--prize", "--min-fit", "4", "--top", "5")
    rows = env["data"]["rows"]
    assert len(rows) <= 5 and all(
        r["prize_usd_approx"] > 0 and r["ai_lean_fit_1to5"] >= 4 for r in rows
    )
    scores = [r["tractability_score"] for r in rows]
    assert scores == sorted(scores, reverse=True)

    code, env = run("targets", "--tab", "nope")
    assert code == 2 and env["error"]["code"] == "BAD_USAGE"


# ---------------------------------------------------------------- spark (fake ssh/rsync)


def spark_ok(fake, *, itemized="", ssh=None):
    fake.handlers["rsync"] = lambda cmd, kw: (0, itemized, "")
    fake.handlers["ssh"] = ssh or (lambda cmd, kw: (0, "", ""))


def test_unreachable_spark_is_exit_5(repo, run, fake, monkeypatch):
    monkeypatch.setenv("SPARK_SSH_HOST", "nowhere.local")
    fake.handlers["ssh"] = lambda cmd, kw: (255, "", "ssh: Could not resolve hostname")
    code, env = run("spark", "jobs")
    assert code == 5 and env["error"]["code"] == "SPARK_UNREACHABLE"
    assert env["command"] == "spark jobs"
    cmd, kw = fake.of("ssh")[0]
    assert cmd[:6] == ["ssh", "-o", "BatchMode=yes", "-o", "ConnectTimeout=8", "nowhere.local"]
    fake.handlers["rsync"] = lambda cmd, kw: (255, "", "connection unexpectedly closed")
    code, env = run("spark", "sync")
    assert code == 5 and env["error"]["code"] == "SPARK_UNREACHABLE"


def test_sync_excludes_and_fetches_cache_when_manifest_changes(repo, run, fake):
    spark_ok(fake, itemized=">f.st...... erdos/lake-manifest.json\n>f+++++++++ src/x.py\n")
    code, env = run("spark", "sync")
    assert code == 0 and env["data"]["manifest_changed"] is True
    assert env["data"]["changed"] == ["erdos/lake-manifest.json", "src/x.py"]
    cmd, _ = fake.of("rsync")[0]
    assert cmd[:4] == ["rsync", "-az", "-i", "--delete"]
    for ex in (".lake", ".git", ".venv"):
        assert ["--exclude", ex] == cmd[cmd.index(ex) - 1 : cmd.index(ex) + 1]
    assert cmd[-2:] == [f"{repo}/", "sparky.local:lean-work/ctrl/"]
    presync, cache = (k["input"] for _, k in fake.of("ssh"))
    assert "jobs.sh" in presync and "lake-manifest.json" in presync
    assert '"1" = 1' in cache and "lake exe cache get" in cache

    spark_ok(fake, itemized=">f.st...... README.md\n")
    code, env = run("spark", "sync")
    assert env["data"]["manifest_changed"] is False
    assert '"0" = 1' in fake.of("ssh")[-1][1]["input"]


def test_prove_needs_approval_then_returns_job(repo, run, fake):
    spark_ok(fake)
    run("new", "196")
    code, env = run("spark", "prove", "196")
    assert code == 3 and env["error"]["code"] == "NOT_APPROVED"
    assert not fake.of("rsync")  # nothing was sent

    run("approve", "196", "--by", "mike")

    def ssh(cmd, kw):
        if "prove.sh" in kw["input"]:
            return 0, 'starting\n{"job": "20261017-196-prove-1"}\n', ""
        return 0, "", ""

    spark_ok(fake, ssh=ssh)
    code, env = run("spark", "prove", "196", "--minutes", "30", "--attempts", "4")
    assert code == 0 and env["data"]["job"] == "20261017-196-prove-1"
    script = [k["input"] for c, k in fake.of("ssh") if "prove.sh" in k["input"]][0]
    assert "tools/spark/prove.sh" in script
    assert "196 --model leanstral --minutes 30 --attempts 4" in script
    st = status(repo)
    assert st["phase"] == "proving" and st["jobs"][0]["job"] == "20261017-196-prove-1"
    assert env["next"] == [
        "ctrl spark log 20261017-196-prove-1 -f",
        "ctrl spark fetch 20261017-196-prove-1",
    ]


def test_solve_passes_args_after_double_dash(repo, run, fake):
    run("new", "196")
    (repo / "work/196/search.py").write_text("print('hi')\n")
    spark_ok(fake, ssh=lambda cmd, kw: (0, '{"job": "j1"}\n', ""))
    code, env = run("spark", "solve", "196", "search.py", "--", "--n", "18", "--json")
    assert code == 0 and env["data"]["args"] == ["--n", "18", "--json"]
    script = fake.of("ssh")[-1][1]["input"]
    assert "tools/spark/solve.sh" in script and '"$f" 196 search.py --n 18 --json' in script
    code, env = run("spark", "solve", "196", "nope.py")
    assert code == 2 and env["error"]["code"] == "BAD_USAGE"


def test_spark_check_records_remote_result(repo, run, fake):
    approved(run)

    def ssh(cmd, kw):
        if "check.sh" in kw["input"]:
            return 0, check_report(), ""
        return 0, "", ""

    spark_ok(fake, ssh=ssh)
    code, env = run("spark", "check", "196")
    assert code == 0 and env["data"]["results"][0]["ok"]
    assert status(repo)["last_spark_check"]["ok"] is True
    assert status(repo)["phase"] == "approved"  # only local checks move the phase


def remote(*, jobs=None, meta=None, log="line1\n", manifest_sha="", prove_job=None):
    """A fake Spark: answers the presync probe, tools/spark/*.sh, meta.json and the cache step."""

    def ssh(cmd, kw):
        script = kw["input"]
        if "@@manifest@@" in script:
            return 0, json.dumps(jobs or []) + "\n@@manifest@@\n" + manifest_sha + "\n", ""
        if "jobs.sh" in script:
            return 0, json.dumps(jobs or []), ""
        if "log.sh" in script:
            return (5, "", "job not found") if '"$f" missing' in script else (0, log, "")
        if "meta.json; [ -f" in script:
            return (44, "", "") if "/missing/" in script else (0, json.dumps(meta or {}), "")
        if "prove.sh" in script:
            return 0, json.dumps({"job": prove_job or "j-prove"}) + "\n", ""
        return 0, "", ""

    return ssh


def test_sync_refuses_manifest_change_while_prove_runs(repo, run, fake):
    running = [{"job": "j9", "kind": "prove", "status": "running"}]
    local = sha(repo / "erdos/lake-manifest.json")
    spark_ok(fake, ssh=remote(jobs=running, manifest_sha="0" * 64))
    code, env = run("spark", "sync")
    assert code == 3 and env["error"]["code"] == "JOB_RUNNING"
    assert "--force" in env["error"]["hint"] and not fake.of("rsync")
    code, env = run("spark", "sync", "--force")
    assert code == 0 and fake.of("rsync")
    # same manifest: syncing source files under a running prove job is fine
    spark_ok(fake, ssh=remote(jobs=running, manifest_sha=local))
    assert run("spark", "sync")[0] == 0
    # finished jobs never block
    done = [{"job": "j8", "kind": "prove", "status": "success"}]
    spark_ok(fake, ssh=remote(jobs=done, manifest_sha="0" * 64))
    assert run("spark", "sync")[0] == 0


def test_prove_and_solve_pass_env_knobs(repo, run, fake):
    approved(run)
    spark_ok(fake, ssh=remote(prove_job="j-p"))
    code, env = run("spark", "prove", "196", "--reasoning", "none", "--max-turns", "40")
    assert code == 0 and env["data"]["env"] == {"PROVE_REASONING": "none", "PROVE_MAX_TURNS": "40"}
    script = [k["input"] for _, k in fake.of("ssh") if "prove.sh" in k["input"]][-1]
    assert 'PROVE_REASONING=none PROVE_MAX_TURNS=40 bash "$f" 196 --model leanstral' in script
    code, env = run("spark", "prove", "196", "--reasoning", "low")
    assert code == 2 and env["error"]["code"] == "BAD_USAGE"

    (repo / "work/196/search.py").write_text("")
    spark_ok(fake, ssh=lambda cmd, kw: (0, '{"job": "j-s"}\n', ""))
    code, env = run("spark", "solve", "196", "search.py", "--timeout-min", "15")
    assert code == 0
    assert 'SOLVE_TIMEOUT_MIN=15 bash "$f" 196 search.py' in fake.of("ssh")[-1][1]["input"]


def test_jobs_log_fetch(repo, run, fake):
    run("new", "196")
    jobs = [
        {"job": "j2", "nnn": "196", "kind": "prove", "status": "running", "started": "b"},
        {"job": "j1", "nnn": "196", "kind": "prove", "status": "success", "started": "a"},
    ]
    meta = {"job": "j1", "nnn": "196", "kind": "prove", "status": "success"}
    spark_ok(fake, itemized=">f+++++++++ final.lean\n", ssh=remote(jobs=jobs, meta=meta))
    code, env = run("spark", "jobs")
    assert code == 0 and [r["job"] for r in env["data"]["jobs"]] == ["j2", "j1"]
    assert env["next"] == ["ctrl spark log j2 -f", "ctrl spark fetch j1"]

    code, env = run("spark", "log", "j1", "-n", "50")
    assert code == 0 and env["data"]["log"] == "line1\n"
    assert "log.sh" in fake.of("ssh")[-1][1]["input"]
    assert '"$f" j1 -n 50' in fake.of("ssh")[-1][1]["input"]
    code, env = run("spark", "log", "missing")
    assert code == 5 and env["error"]["code"] == "JOB_NOT_FOUND"
    code, env = run("spark", "log", "../etc")
    assert code == 2 and env["error"]["code"] == "BAD_USAGE"
    code, env = run("spark", "log", "j1", "-f")
    assert code == 2  # -f streams raw text, so not with --json

    dest = repo / "work/196/candidates/j1"
    dest.mkdir(parents=True)
    (dest / "final.lean").write_text("x")  # what the fake rsync would have pulled
    code, env = run("spark", "fetch", "j1")
    assert code == 0 and env["data"]["dest"] == "work/196/candidates/j1"
    assert env["data"]["files"] == ["final.lean"]
    assert env["data"]["candidate"] == "work/196/candidates/j1/final.lean"
    assert env["next"] == ["ctrl promote 196 j1", "ctrl check 196 --fast"]
    cmd, _ = fake.of("rsync")[-1]
    assert cmd[-2:] == ["sparky.local:lean-work/jobs/j1/outputs/", f"{dest}/"]
    assert "fetched job `j1`" in (repo / "work/196/log.md").read_text()
    code, env = run("spark", "fetch", "missing")
    assert code == 5 and env["error"]["code"] == "JOB_NOT_FOUND"


# ---------------------------------------------------------------- promote


def candidate(repo, job="j1", *, final="theorem solution : statement := by\n  decide\n", diff=""):
    d = repo / "work/196/candidates" / job
    (d / "attempt-1").mkdir(parents=True)
    (d / "attempt-1/challenge.diff").write_text(diff)
    if final is not None:
        (d / "final.lean").write_text(final)
    return d


def test_promote_copies_then_checks(repo, run, fake):
    approved(run)
    candidate(repo)
    checksh(fake)
    code, env = run("promote", "196", "j1")
    assert code == 0 and env["data"]["promoted"] is True
    sol = (repo / "erdos/ErdosLab/Erdos196.lean").read_text()
    assert "decide" in sol
    assert fake.of("bash")[-1][0] == ["bash", "scripts/check.sh", "196", "--fast"]
    assert env["next"][0] == "ctrl check 196"


def test_promote_restores_on_failed_check(repo, run, fake):
    approved(run)
    sol = repo / "erdos/ErdosLab/Erdos196.lean"
    before = sol.read_text()
    candidate(repo)
    checksh(fake, rc=4, out=check_report(binding={"ok": False, "detail": "restated"}))
    code, env = run("promote", "196", "j1")
    assert code == 4 and env["error"]["code"] == "BINDING_MISMATCH"
    assert env["data"]["restored"] is True and sol.read_text() == before


def test_promote_refuses_challenge_edits_and_missing_files(repo, run, fake):
    approved(run)
    sol = repo / "erdos/ErdosLab/Erdos196.lean"
    before = sol.read_text()
    candidate(repo, "dirty", diff="Files a/Challenge/Erdos196.lean and b/... differ\n")
    code, env = run("promote", "196", "dirty")
    assert code == 4 and env["error"]["code"] == "CHALLENGE_DRIFT"
    assert sol.read_text() == before and not fake.of("bash")
    candidate(repo, "nofinal", final=None)
    code, env = run("promote", "196", "nofinal")
    assert code == 2 and env["error"]["fix"] == "ctrl spark fetch nofinal"


# ---------------------------------------------------------------- doctor


def _fake_home(repo, tmp_path):
    home = tmp_path / "home"
    for tool in ("elan", "lake"):
        p = home / ".elan" / "bin" / tool
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text("#!/bin/sh\n")
        p.chmod(0o755)
    lean = home / ".elan/toolchains/leanprover--lean4---v4.33.1/bin/lean"
    lean.parent.mkdir(parents=True)
    lean.write_text("")
    pkgs = repo / "erdos/.lake/packages"
    (pkgs / "mathlib/.lake/build/lib").mkdir(parents=True)
    (pkgs / "formal_conjectures/.git").mkdir(parents=True)
    (pkgs / "formal_conjectures/.git/HEAD").write_text(PIN + "\n")


def test_doctor_local_and_remote(repo, run, fake, tmp_path, monkeypatch):
    fake.handlers["elan"] = lambda cmd, kw: (0, "elan 4.1.2\n", "")
    fake.handlers["uv"] = lambda cmd, kw: (0, "uv 0.13.1\n", "")
    monkeypatch.setattr("ctrl.proc.which", _which(tmp_path))
    code, env = run("doctor", "--no-remote")
    names = {c["name"]: c for c in env["data"]["checks"]}
    assert code == 1 and env["error"]["code"] == "TOOL_MISSING"
    assert names["toolchain"]["ok"] is False and "v4.33.1" in names["toolchain"]["detail"]

    _fake_home(repo, tmp_path)
    code, env = run("doctor", "--no-remote")
    assert code == 0, [c for c in env["data"]["checks"] if not c["ok"]]
    assert all(c["where"] == "mac" for c in env["data"]["checks"])
    assert {"elan", "lake", "toolchain", "uv", "lean packages", "lean cache", "fc pin"} <= {
        c["name"] for c in env["data"]["checks"]
    }

    lines = [
        {"name": "elan", "ok": True, "detail": "elan 4.1.2"},
        {"name": "kissat", "ok": True, "detail": "4.0.4"},
        {"name": "leanstral", "ok": False, "detail": "no ollama model named leanstral"},
    ]
    fake.handlers["ssh"] = lambda cmd, kw: (0, "\n".join(map(json.dumps, lines)) + "\n", "")
    code, env = run("doctor", "--remote")
    spark_checks = [c for c in env["data"]["checks"] if c["where"] == "spark"]
    assert [c["name"] for c in spark_checks] == ["ssh", "elan", "kissat", "leanstral"]
    assert code == 1 and "leanstral" in env["error"]["message"]
    script = fake.of("ssh")[-1][1]["input"]
    assert "leanprover--lean4---v4.33.1" in script and "venvs/solve" in script
    for probe in (
        "ollama show leanstral",
        "tmux",
        ".local/bin",
        "tools/spark/env.sh",
        "packages/mathlib",
    ):
        assert probe in script
    assert len(fake.of("ssh")) == 1  # all remote checks in one call

    fake.handlers["ssh"] = lambda cmd, kw: (255, "", "ssh: connect timed out")
    code, env = run("doctor")
    assert code == 5 and env["error"]["code"] == "SPARK_UNREACHABLE"


def _which(tmp_path):
    def which(name, *extra):
        home = tmp_path / "home" / ".elan" / "bin" / name
        if name in ("elan", "lake"):
            return str(home) if home.exists() else None
        return f"/usr/bin/{name}"

    return which


# ---------------------------------------------------------------- integration (real Lean / SSH)


@pytest.mark.integration
def test_real_doctor_remote():
    import subprocess

    cp = subprocess.run(["uv", "run", "ctrl", "doctor", "--json"], capture_output=True, text=True)
    env = json.loads(cp.stdout)
    assert set(env) == ENVELOPE_KEYS
    assert any(c["where"] == "spark" for c in env["data"]["checks"])
