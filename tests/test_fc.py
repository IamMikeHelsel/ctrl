"""Statement extraction from real Formal Conjectures files. Faithfulness starts here."""

from __future__ import annotations

from pathlib import Path

from erdos_lab import fc

FC = Path(__file__).parent / "fixtures" / "FormalConjectures" / "ErdosProblems"


def theorems(nnn: str) -> list[fc.Theorem]:
    return fc.candidates(fc.parse((FC / f"{nnn}.lean").read_text()), nnn)


def test_single_theorem_is_copied_verbatim_with_namespace():
    [t] = theorems("196")
    assert t.full_name == "Erdos196.erdos_196"
    assert t.category == "research open"
    assert t.binders == ""
    assert t.statement == "∀ (f : ℕ ≃ ℕ), HasMonotoneAP f 4"
    assert not t.needs_answer


def test_parts_and_multiline_statements():
    i, ii = theorems("834")
    assert [i.name, ii.name] == ["erdos_834.parts.i", "erdos_834.parts.ii"]
    assert i.opens == ["Filter Asymptotics"]
    assert i.statement.startswith("¬ ∃ (n : ℕ) (H : Finset (Finset (Fin n))),\n")
    assert i.statement.rstrip().endswith("∀ v : Fin n, 7 ≤ H.hypergraphDegree v")
    assert ":=" not in i.statement and "sorry" not in i.statement


def test_binders_become_a_forall():
    ts = {t.name: t for t in theorems("895")}
    assert list(ts) == ["erdos_895", "erdos_895.variants.eighteen", "erdos_895.variants.hindman"]
    s = ts["erdos_895.variants.eighteen"].statement
    assert s.startswith("∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n))")
    assert "(hG : G.CliqueFree 3),\n" in s
    assert s.rstrip().endswith("G.IsIndepSet {a, b, c}")
    # `open Filter` sits before `namespace Erdos895` and is still in scope
    assert ts["erdos_895"].opens == ["Filter"]
    assert ts["erdos_895"].statement.startswith("∀ᶠ n in atTop,")


def test_sorry_answers_are_detected():
    [t] = theorems("1157")
    assert "erdos_1157.answer" in t.needs_answer
    ts = {t.name: t for t in theorems("1074")}
    # helper theorems (two_not_mem_pillaiPrimes, ...) are not problem statements
    assert all(n.startswith("erdos_1074") for n in ts)
    assert not ts["erdos_1074.parts.i"].needs_answer
    assert "erdos_1074.parts.ii.answer" in ts["erdos_1074.parts.ii"].needs_answer
    assert ts["erdos_1074.parts.iv"].needs_answer
    assert fc.sorry_defs((FC / "1074.lean").read_text()) == [
        "erdos_1074.parts.ii.answer",
        "erdos_1074.parts.iv.answer",
    ]


def test_answer_sorry_open_in_comments_and_strings():
    ts = {t.name: t for t in theorems("9001")}
    assert list(ts) == ["erdos_9001", "erdos_9001.variants.easy"]  # docstring decl ignored
    assert "answer(sorry)" in ts["erdos_9001"].needs_answer
    assert ts["erdos_9001"].category == "research open"  # the `--` inside the URL is not a comment
    easy = ts["erdos_9001.variants.easy"]
    assert easy.open_in == ["Real"]
    assert easy.opens == ["Filter"]
    assert easy.statement.startswith("∀ {x : ℝ} (hx : 0 < x),\n")
    assert "-- an inline comment" in easy.statement  # verbatim, comments kept
    assert "(fun z => z) y = x" in easy.statement


def test_strip_comments_keeps_offsets():
    src = 'a /- x /- nested -/ y -/ b -- tail\n"s -- not a comment" c'
    out = fc.strip_comments(src)
    assert len(out) == len(src)
    assert out.split() == ["a", "b", '"s', "--", "not", "a", 'comment"', "c"]


def test_challenge_matches_the_build_verified_834_byte_for_byte():
    """tests/fixtures/golden/Erdos834.lean is the shape the Lean agent verified in a real build."""
    t = fc.pick(theorems("834"), "parts.ii")
    text = fc.challenge_text("834", t, "d9ce556af8ed4bdbd0ede2ed588d7cf4bb76cfdd")
    assert text == (FC.parents[1] / "golden" / "Erdos834.lean").read_text()


def test_challenge_and_solution_text():
    [t] = theorems("196")
    text = fc.challenge_text("196", t, "d9ce556af8ed")
    lines = text.splitlines()
    assert lines[0] == "import FormalConjectures.ErdosProblems.«196»"
    assert "Statement copied verbatim from `Erdos196.erdos_196`" in text
    assert "(google-deepmind/formal-conjectures @ d9ce556, Apache-2.0)" in text
    assert "Source: https://www.erdosproblems.com/196" in text
    # opens precede the namespace: inside it, `open Erdos196` would resolve to Challenge.Erdos196
    assert text.index("open Erdos196") < text.index("namespace Challenge.Erdos196")
    assert "def statement : Prop :=\n    ∀ (f : ℕ ≃ ℕ), HasMonotoneAP f 4\n" in text
    assert lines[-3:] == ["-- approved-by: (pending)", "", "end Challenge.Erdos196"]
    sol = fc.solution_text("196")
    assert "import Challenge.Erdos196" in sol
    assert "theorem solution : statement := by\n  sorry" in sol


def test_open_in_is_emitted_on_the_def():
    t = {t.name: t for t in theorems("9001")}["erdos_9001.variants.easy"]
    text = fc.challenge_text("9001", t, "pin")
    assert "open Real in\n/-- statement copied from" in text
    assert "open Erdos9001\nopen Filter\n" in text


def test_approval_line_roundtrip():
    text = "x\n-- approved-by: (pending)\n"
    assert not fc.is_approved_line(fc.approval_line(text))
    new = fc.set_approval(text, "-- approved-by: mike 2026-10-17")
    assert new == "x\n-- approved-by: mike 2026-10-17\n"
    assert fc.is_approved_line(fc.approval_line(new))


def test_add_import_is_idempotent_and_after_comments():
    root = "-- Frozen statements.\n"
    once = fc.add_import(root, "Challenge.Erdos196")
    assert once == "-- Frozen statements.\nimport Challenge.Erdos196\n"
    assert fc.add_import(once, "Challenge.Erdos196") == once
    twice = fc.add_import(once, "Challenge.Erdos834")
    assert twice.splitlines()[1:] == ["import Challenge.Erdos196", "import Challenge.Erdos834"]


def test_pick_by_full_name_or_suffix():
    ts = theorems("895")
    assert fc.pick(ts, "erdos_895").name == "erdos_895"
    assert fc.pick(ts, "eighteen").name == "erdos_895.variants.eighteen"
    assert fc.pick(ts, "Erdos895.erdos_895.variants.hindman").name.endswith("hindman")
    assert fc.pick(ts, "nope") is None
