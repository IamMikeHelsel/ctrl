import Mathlib.Tactic
namespace M06Moment

/-- Normalized degree moment identity, assuming the mean equation explicitly. -/
theorem centered_moment {V : Type*} (s : Finset V) (d : V → ℝ) (r : ℝ)
    (hmean : ∑ v ∈ s, d v = (s.card : ℝ) * r) :
    (∑ v ∈ s, (d v-r)^2) = (∑ v ∈ s, (d v)^2) - (s.card : ℝ)*r^2 := by
  calc
    _ = ∑ v ∈ s, ((d v)^2 - 2*r*d v + r^2) := by
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
        nsmul_eq_mul, ← Finset.mul_sum]
      rw [hmean]
      ring

/-- Graph semantics enter as the exact sum of neighborhood crossing counts. -/
theorem some_neighbor_variance {V : Type*} (s : Finset V) (hs : s.Nonempty)
    (d c : V → ℝ) (r variance : ℝ)
    (hmean : ∑ v ∈ s, d v = (s.card : ℝ)*r)
    (hcross : ∑ v ∈ s, c v = ∑ v ∈ s, (d v)^2)
    (hvariance : ∑ v ∈ s, (d v-r)^2 = (s.card : ℝ)*variance) :
    ∃ v ∈ s, r^2+variance ≤ c v := by
  by_contra h
  push_neg at h
  have hlt := Finset.sum_lt_sum_of_nonempty hs h
  have hm := centered_moment s d r hmean
  simp only [Finset.sum_const, nsmul_eq_mul] at hlt
  nlinarith

#print axioms centered_moment
#print axioms some_neighbor_variance
end M06Moment
