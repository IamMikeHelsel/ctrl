/- Synthetic fixture (not from FC): the older `answer(sorry)` style, an `open … in` prefix,
   a string containing `--`, and a nested /- block -/ comment. -/
import FormalConjecturesUtil

open Filter

namespace Erdos9001

/-- A docstring with `theorem fake : False := by` inside it. -/
@[category research open, AMS 11, formal_proof using lean4 at "https://x.org/a--b"]
theorem erdos_9001 : answer(sorry) ↔ ∀ n : ℕ, n = n := by
  sorry

open Real in
@[category research solved, AMS 11]
theorem erdos_9001.variants.easy {x : ℝ} (hx : 0 < x) :
    -- an inline comment
    ∃ y : ℝ, y = x ∧ (fun z => z) y = x := by
  exact ⟨x, rfl, rfl⟩

end Erdos9001
