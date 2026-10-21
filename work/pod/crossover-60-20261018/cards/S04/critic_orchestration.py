"""Actual orchestration code with explicit fake subprocesses, in isolated copies.

No Lean claim: this tests manifest timing and provenance bookkeeping only.
"""

import contextlib
import hashlib
import importlib.util
import io
import json
import shutil
import sys
import types
from pathlib import Path
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
SOURCE = Path("/Users/mike/Dev/ctrl-research-notebook/research-notebook/lean-controls")
ROOT = HERE / "critic_orchestration_cases"
ROOT.mkdir(exist_ok=True)


def sha(b):
    return hashlib.sha256(b).hexdigest()


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def fresh(name):
    p = ROOT / name
    if p.exists():
        shutil.rmtree(p)
    for d in [
        "scripts",
        "benchmarks",
        "LeanControls/Generated",
        "evidence/benchmarks",
        "evidence/uncertainty-artifact",
    ]:
        (p / d).mkdir(parents=True, exist_ok=True)
    return p


def fake_runtime(_p):
    return "MOCK-LAKE", {}


generate = types.ModuleType("generate_interval_certificate")
runtime = types.ModuleType("lean_runtime")
runtime.runtime = fake_runtime
produced = []


def produce(data, name):
    produced.append(json.loads(json.dumps(data)))
    source = f"namespace LeanControls.Generated.{name}\n-- input decay {data['decay_margin']}\ntheorem checked : True := True.intro\nend LeanControls.Generated.{name}\n"
    witness = {
        "dimension": 2,
        "degree": 2,
        "partition": ["0", "1/2"],
        "decay_margin": data["decay_margin"],
        "energy_lower": "1",
        "energy_upper": "6",
    }
    return source, witness


generate.produce = produce
with patch.dict(sys.modules, {"generate_interval_certificate": generate, "lean_runtime": runtime}):
    benchmark = load("critic_original_benchmark", SOURCE / "scripts/verify_benchmarks.py")
    project = load("critic_original_project", SOURCE / "scripts/verify_project.py")
project.platform.platform = lambda: "EXPLICIT MOCK PLATFORM"

# Test1: original verifier binds post-run input bytes, not the bytes consumed by produce.
p = fresh("benchmark_input_race")
benchmark.PROJECT = p
benchmark.CASES = [("double-integrator", "DoubleIntegrator")]
(p / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
(p / "lake-manifest.json").write_text(
    json.dumps({"packages": [{"name": "mathlib", "rev": "test-revision"}]})
)
model = p / "benchmarks/double-integrator.json"
old = (SOURCE / "benchmarks/double-integrator.json").read_bytes()
model.write_bytes(old)
new = json.loads(old)
new["decay_margin"] = "2"
newbytes = (json.dumps(new) + "\n").encode()


def benchmark_run(command, **kwargs):
    assert command[0] == "MOCK-LAKE"
    # Simulated concurrent writer after production and before manifest hashing.
    model.write_bytes(newbytes)
    return types.SimpleNamespace(
        returncode=0,
        stdout="'LeanControls.Generated.DoubleIntegrator.checked' does not depend on any axioms\n",
        stderr="",
    )


with (
    patch.object(benchmark.subprocess, "run", benchmark_run),
    contextlib.redirect_stdout(io.StringIO()),
):
    benchmark.main()
m = json.loads((p / "evidence/benchmarks/verification.json").read_text())
assert m["status"] == "verified" and produced[-1]["decay_margin"] == "1"
assert m["cases"][0]["input_bytes_sha256"] == sha(newbytes) != sha(old)
benchmark_case = {
    "manifest_status": m["status"],
    "consumed_model_decay": produced[-1]["decay_margin"],
    "recorded_file_decay": json.loads(model.read_text())["decay_margin"],
    "consumed_bytes_sha256": sha(old),
    "recorded_input_sha256": m["cases"][0]["input_bytes_sha256"],
    "finding": "Input hash is for later bytes, not parsed production bytes",
}


def seed_project(name):
    p = fresh(name)
    for fn in [
        "LeanControls.lean",
        "Audit.lean",
        "lean-toolchain",
        "lakefile.toml",
        "check.sh",
        "requirements.txt",
    ]:
        (p / fn).write_text("original " + fn + "\n")
    (p / "lake-manifest.json").write_text("{}\n")
    (p / "LeanControls/Example.lean").write_text(
        "-- version A\ntheorem example : True := True.intro\n"
    )
    (p / "benchmarks/model.json").write_text('{"model":"A"}\n')
    (p / "scripts/verify_project.py").write_bytes(
        (SOURCE / "scripts/verify_project.py").read_bytes()
    )
    (p / "evidence/axioms.json").write_text('{"example": []}\n')
    for f in ["benchmarks/verification.json", "uncertainty-artifact/verification.json"]:
        (p / "evidence" / f).write_text('{"status":"mock-verified"}\n')
    project.PROJECT = p
    return p


# Test2: actual pre/post guard detects a persistent mutation (positive control).
# Test3: actual guard accepts an A->B->A interleaving, even though mock build reads B.
project_cases = []
for mode in ["persistent", "ABA"]:
    p = seed_project("project_" + mode)
    path = p / "LeanControls/Example.lean"
    a = path.read_bytes()
    b = a.replace(b"version A", b"version B")
    observed = []

    def project_run(command, path=path, a=a, b=b, observed=observed, mode=mode, **kwargs):
        if command == ["sh", "check.sh"]:
            path.write_bytes(b)
            observed.append(sha(path.read_bytes()))
            if mode == "ABA":
                path.write_bytes(a)
        return types.SimpleNamespace(
            returncode=0, stdout="EXPLICIT MOCK subprocess success\n", stderr=""
        )

    caught = None
    with (
        patch.object(project.subprocess, "run", project_run),
        contextlib.redirect_stdout(io.StringIO()),
    ):
        try:
            project.main()
        except RuntimeError as exc:
            caught = str(exc)
    report = json.loads((p / "evidence/project-verification.json").read_text())
    assert report["status"] == ("failed" if mode == "persistent" else "verified")
    assert observed == [sha(b)]
    if mode == "ABA":
        assert report["source_sha256"]["LeanControls/Example.lean"] == sha(a) != observed[0]
    project_cases.append(
        {
            "mode": mode,
            "status": report["status"],
            "mock_build_read_sha256": observed[0],
            "recorded_source_sha256": report["source_sha256"]["LeanControls/Example.lean"],
            "caught": caught,
        }
    )

# Test4: runtime fails before a new running marker is saved; old success survives.
p = seed_project("project_stale_preflight")
status = p / "evidence/project-verification.json"
stale = {"status": "verified", "started_utc": "OLD-ATTEMPT", "finished_utc": "OLD-ATTEMPT"}
status.write_text(json.dumps(stale) + "\n")
before = status.read_bytes()


def broken_runtime(_p):
    raise RuntimeError("synthetic missing Lake")


with patch.object(project, "runtime", broken_runtime):
    try:
        project.main()
    except RuntimeError as exc:
        assert str(exc) == "synthetic missing Lake"
    else:
        raise AssertionError("expected preflight failure")
assert status.read_bytes() == before
out = {
    "status": "all expected bookkeeping outcomes reproduced",
    "subprocesses": "ALL MOCKED; no Lean build or mathematical theorem acceptance occurred",
    "originals": "read only",
    "benchmark_input_race": benchmark_case,
    "project_source_guard": project_cases,
    "stale_preflight": {
        "new_call": "raised RuntimeError",
        "old_marker": json.loads(status.read_text()),
        "scope": "A consumer must check this invocation result, not only stored status",
    },
    "source_hashes": {
        n: sha((SOURCE / "scripts" / n).read_bytes())
        for n in ["verify_benchmarks.py", "verify_project.py"]
    },
}
(HERE / "critic_orchestration.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
