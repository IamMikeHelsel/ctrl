"""Exercise the main ControlsLean source policy without running Lean or accessing runners."""

import importlib.util
from pathlib import Path

import pytest

SPEC = importlib.util.spec_from_file_location(
    "controls_source_guard", Path(__file__).parents[1] / "scripts" / "check_tokens.py"
)
assert SPEC is not None and SPEC.loader is not None
GUARD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GUARD)


@pytest.mark.parametrize(
    "source,token",
    [
        ("theorem bad : True := by sorry", "sorry"),
        ('def s := s!"{(by sorry : Nat)}"', "sorry"),
        ("theorem bad : True := by admit", "admit"),
        ("  axiom bad : False", "axiom"),
        ("theorem bad : True := by native_decide", "native_decide"),
        ("@[implemented_by unsafeVersion] def checked := 1", "implemented_by"),
        ("def quote := '\"'\ntheorem bad : True := by sorry", "sorry"),
        ('def s := "escaped \\" text"\ntheorem bad : True := by admit', "admit"),
        ('def s := r#"quoted " native_decide"#\n axiom bad : False', "axiom"),
    ],
)
def test_forbidden_code_is_rejected(source, token):
    assert [t for _, t in GUARD.violations(source)] == [token]


def test_comments_strings_and_similar_identifiers_are_not_code():
    source = """/- sorry /- admit -/ native_decide -/
-- axiom ignored : False
def text := "implemented_by \\"sorry\\""
def raw := r##"sorry " admit native_decide"##
def sorry_count := 0
def native_decide_test := 0
def theorem' := 1
"""
    assert GUARD.violations(source) == []


def test_line_positions_survive_nested_comments():
    assert GUARD.violations("/- first\n/- second -/\n-/\n  axiom bad : False") == [(4, "axiom")]


def test_cli_return_codes_and_actual_sources(tmp_path, capsys):
    assert GUARD.main([]) == 2
    path = tmp_path / "Bad.lean"
    path.write_text("/- admissible comment: sorry -/\nby native_decide\n")
    assert GUARD.main([str(path)]) == 1
    assert ":2: forbidden token native_decide" in capsys.readouterr().out
    root = Path(__file__).parents[1]
    paths = sorted((root / "ControlsLean").rglob("*.lean"))
    assert paths and GUARD.main([str(p) for p in paths]) == 0
