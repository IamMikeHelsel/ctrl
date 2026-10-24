"""Parser tests for tools/mathdb (no index or corpora needed)."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "mathdb"))

from lean_parse import parse_lean  # noqa: E402

SRC = '''namespace Foo
/-- The sum of two naturals is commutative. -/
theorem add_comm' (a b : ℕ) : a + b = b + a := by
  omega

@[simp] lemma bar {x : ℝ} (h : 0 < x) : 0 ≤ x := le_of_lt h
-- theorem commented_out : True := trivial
/- block
theorem also_commented : True := trivial
-/
def baz : ℕ := 3
end Foo

theorem top_level : True := trivial
'''


class ParseTests(unittest.TestCase):
    def setUp(self):
        self.decls = {d.name: d for d in parse_lean(SRC)}

    def test_names_and_namespaces(self):
        self.assertEqual(set(self.decls), {"Foo.add_comm'", "Foo.bar", "Foo.baz", "top_level"})

    def test_comments_are_skipped(self):
        self.assertFalse(any("commented" in n for n in self.decls))

    def test_signature_docstring_attrs(self):
        d = self.decls["Foo.add_comm'"]
        self.assertEqual(d.kind, "theorem")
        self.assertEqual(d.signature, "(a b : ℕ) : a + b = b + a")
        self.assertEqual(d.doc, "The sum of two naturals is commutative.")
        self.assertEqual(d.line, 3)
        b = self.decls["Foo.bar"]
        self.assertEqual(b.attrs, "@[simp]")
        self.assertEqual(b.doc, "")


if __name__ == "__main__":
    unittest.main()
