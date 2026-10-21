import domain_clock
noncomputable section
set_option autoImplicit false
namespace S02Processing
open LeanControls.ConstructiveHold S02Clock

/-- Reserve processing/actuation readiness inside the unchanged total latency.
The quantities are bounds on elapsed physical time, not callback timestamps. -/
theorem end_to_end_budget (network processing : ℕ → ℝ) (reserve : ℝ)
    (hn : ∀ n, 0≤network n ∧ network n≤h-reserve)
    (hp : ∀ n, 0≤processing n ∧ processing n≤reserve) :
    ∀ n, 0≤network n+processing n ∧ network n+processing n≤h := by
  intro n
  constructor <;> linarith [(hn n).1,(hn n).2,(hp n).1,(hp n).2]

theorem reserved_processing_preserves_release
    (network processing : ℕ → ℝ) (reserve : ℝ)
    (hn : ∀ n, 0≤network n ∧ network n≤h-reserve)
    (hp : ∀ n, 0≤processing n ∧ processing n≤reserve) (n : ℕ) :
    release (fun j => network j+processing j) n=grid n+h := by
  exact release_eq _ (fun j => (end_to_end_budget network processing reserve hn hp j).2) n

/-- A positive unbudgeted post-network delay invalidates the original deadline.
This says nothing about whether the delayed physical trajectory is unsafe. -/
theorem no_endpoint_slack (processing : ℝ) (hp : 0<processing) :
    h<h+processing ∧ (1/1000:ℝ)<1/1000+processing := by
  constructor <;> linarith

theorem one_microsecond_outside_source :
    (1/2000:ℝ)+1/1000000>1/2000 ∧
    (1/1000:ℝ)+1/1000000>1/1000 := by norm_num

#print axioms end_to_end_budget
#print axioms reserved_processing_preserves_release
#print axioms no_endpoint_slack
#print axioms one_microsecond_outside_source
end S02Processing
