import domain_clock
noncomputable section
set_option autoImplicit false
namespace S02Queue
open LeanControls LeanControls.ConstructiveHold S02Clock

/-- Inclusive receive-before-release semantics admits at most two consecutive
indices in the queue, including the packet committed at that same instant. -/
theorem inclusive_queue_span (latency : ℕ → ℝ)
    (hb : ∀ n, 0≤latency n ∧ latency n≤h) (i j : ℕ) (t : ℝ)
    (hi : t≤release latency i) (hj : arrival latency j≤t) : j ≤ i+1 := by
  rw [release_eq latency (fun n => (hb n).2) i] at hi
  have hlat := (hb j).1
  dsimp [arrival,grid] at hj hi
  norm_num at hi
  have hc : (j:ℝ)≤(i:ℝ)+1 := by linarith
  exact_mod_cast hc

/-- Between commits, two distinct increasing indices cannot both be queued. -/
theorem strict_queue_span (latency : ℕ → ℝ)
    (hb : ∀ n, 0≤latency n ∧ latency n≤h) (i j : ℕ) (t : ℝ)
    (hi : t<release latency i) (hj : arrival latency j≤t) : j ≤ i := by
  rw [release_eq latency (fun n => (hb n).2) i] at hi
  have hlat := (hb j).1
  dsimp [arrival,grid] at hj hi
  norm_num at hi
  have hc : (j:ℝ)<(i:ℝ)+1 := by linarith
  have hn : j < i+1 := by exact_mod_cast hc
  omega

/-- Strict reordering is possible only after expanding the original bound.
Here the earlier packet has .75ms latency, greater than the allowed .5ms. -/
theorem expanded_bound_reversal :
    (0:ℝ)+3/4000 > 1/2000+0 ∧ (3/4000:ℝ)>h ∧
    (3/4000:ℝ)+h>1/1000 := by norm_num

#print axioms inclusive_queue_span
#print axioms strict_queue_span
#print axioms expanded_bound_reversal

theorem inclusive_queue_card (latency : ℕ → ℝ)
    (hb : ∀ n, 0≤latency n ∧ latency n≤h) (Q : Finset ℕ) (t : ℝ)
    (hq : ∀ n∈Q, arrival latency n≤t ∧ t≤release latency n) : Q.card≤2 := by
  classical
  by_cases hn : Q.Nonempty
  · let i := Q.min' hn
    have hi : i∈Q := Finset.min'_mem Q hn
    have hs : Q⊆{i,i+1} := by
      intro j hj
      have hlo : i≤j := Finset.min'_le Q j hj
      have hhi := inclusive_queue_span latency hb i j t (hq i hi).2 (hq j hj).1
      have hj' : j=i ∨ j=i+1 := by omega
      simpa using hj'
    have hc := Finset.card_le_card hs
    have hne : i≠i+1 := by omega
    simpa [hne] using hc
  · have he : Q=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [he]

theorem strict_queue_card (latency : ℕ → ℝ)
    (hb : ∀ n, 0≤latency n ∧ latency n≤h) (Q : Finset ℕ) (t : ℝ)
    (hq : ∀ n∈Q, arrival latency n≤t ∧ t<release latency n) : Q.card≤1 := by
  classical
  by_cases hn : Q.Nonempty
  · obtain ⟨i,hi⟩ := hn
    have hs : Q⊆{i} := by
      intro j hj
      have hji := strict_queue_span latency hb i j t (hq i hi).2 (hq j hj).1
      have hij := strict_queue_span latency hb j i t (hq j hj).2 (hq i hi).1
      simpa using le_antisymm hji hij
    simpa using Finset.card_le_card hs
  · have he : Q=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [he]

#print axioms inclusive_queue_card
#print axioms strict_queue_card
end S02Queue
