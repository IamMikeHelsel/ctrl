"""Proof-only factory gates: frozen binding and rejection paths, no Lean or SSH."""

import importlib.util
import json
from pathlib import Path
from types import SimpleNamespace

import pytest

ROOT = Path(__file__).resolve().parents[1]


def module(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / "tools/factory" / f"{name}.py")
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


CHECK = module("check")


@pytest.mark.parametrize(
    "proof",
    [
        "sorry",
        "admit",
        "exact native_decide",
        "axiom fake : False",
        "set_option maxHeartbeats 0",
        "run_tac pure ()",
        "#print axioms fake",
        "end Factory",
        "theorem solution : True := by trivial",
        "/-",
        "-- comment",
        "",
    ],
)
def test_rejects_escape_or_statement_replacement(proof):
    with pytest.raises(ValueError):
        CHECK.assemble({"imports": "import Mathlib", "statement": "  False"}, proof)


def test_binding_is_always_inserted_from_protected_contract():
    source = CHECK.assemble({"imports": "import Mathlib", "statement": "  False"}, "trivial")
    assert "def statement : Prop :=\n  False\n" in source
    assert "theorem solution : statement := by" in source
    assert "example : statement := solution" in source
    assert "#print axioms solution" in source


def test_optional_by_wrapper_does_not_change_binding():
    task = {"imports": "import Mathlib", "statement": "  False"}
    assert CHECK.assemble(task, "by\n  trivial") == CHECK.assemble(task, "trivial")
    with pytest.raises(ValueError):
        CHECK.assemble(task, "by\n")


@pytest.mark.parametrize(
    "output",
    [
        "",
        "'Factory.solution' depends on axioms: [sorryAx]",
        "'Factory.solution' depends on axioms: [Lean.ofReduceBool]",
        "'Factory.solution' depends on axioms: [propext]\nwarning: declaration uses sorry",
        "'Other.solution' depends on axioms: [propext]",
        "'Factory.solution' depends on axioms: [propext]\n'Factory.solution' depends on axioms: []",
    ],
)
def test_audit_fails_closed(output):
    with pytest.raises(ValueError):
        CHECK.audit(output)


def test_wrapped_standard_axiom_audit():
    assert CHECK.audit(
        "'Factory.solution' depends on axioms: [propext,\n Classical.choice, Quot.sound]"
    ) == ["Classical.choice", "Quot.sound", "propext"]
    assert CHECK.audit("'Factory.solution' does not depend on any axioms") == []


def test_prepare_refuses_overwrite_and_copies_original_factory(tmp_path):
    factory = tmp_path / "44"
    (factory / "core").mkdir(parents=True)
    (factory / "core/loop.py").write_text("# synthetic controller fixture\n")
    (factory / "LICENSE").write_text("fixture license\n")
    destination = tmp_path / "run"
    prepare = module("prepare").prepare
    prepare(destination, factory)
    assert (destination / "control/loop.py").read_bytes() == (factory / "core/loop.py").read_bytes()
    tasks = json.loads((destination / "tasks/queue.json").read_text())
    assert {t["class"] for t in tasks} == {"math", "controls", "safety", "vision", "robotics"}
    assert all((destination / "project" / t["files"][0]).read_text() == "" for t in tasks)
    with pytest.raises(ValueError, match="already exists"):
        prepare(destination, factory)


def test_live_preflight_uses_acceptance_resource_limits(tmp_path, monkeypatch):
    """Regression: unrestricted preflight hid the Mathlib address-space failure."""
    for folder in ("control", "build", "acceptance"):
        (tmp_path / folder).mkdir()
    (tmp_path / "control/backend.py").write_text(
        "def limits(): pass\ndef sandbox(command, root, project): return command\n"
    )
    (tmp_path / "acceptance/contracts.json").write_text(
        '[{"imports": "import Mathlib", "statement": "  True"}]'
    )
    supervise = module("supervise")
    calls = []

    def run(command, **kwargs):
        assert kwargs["preexec_fn"].__name__ == "limits"
        calls.append(command)
        # Second compiler probe is deliberately false; all other probes succeed.
        return SimpleNamespace(returncode=1 if len(calls) == 2 else 0, stdout="", stderr="")

    monkeypatch.setattr(supervise.subprocess, "run", run)
    assert all(supervise.preflight(tmp_path).values())
    assert len(calls) == 4


@pytest.mark.parametrize(
    "change",
    [
        {"file": "../../outside.txt"},
        {"file": "/tmp/outside.txt"},
        {"id": "../escape"},
        {"statement": ""},
    ],
)
def test_custom_contract_rejects_unsafe_inputs_before_creating_workspace(tmp_path, change):
    factory = tmp_path / "44"
    (factory / "core").mkdir(parents=True)
    (factory / "core/loop.py").write_text("# fixture\n")
    task = json.loads((ROOT / "tools/factory/contracts.json").read_text())[0]
    contract = tmp_path / "contracts.json"
    contract.write_text(json.dumps([{**task, **change}]))
    destination = tmp_path / "run"
    with pytest.raises(ValueError):
        module("prepare").prepare(destination, factory, contract)
    assert not destination.exists()
