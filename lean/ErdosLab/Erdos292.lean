import Challenge.Erdos292

open Erdos292 Finset

namespace Challenge.Erdos292

theorem solution : statement := by
  rintro n ⟨S, hS_sub, hnS, hS_sum⟩ hn1
  have h1_not_mem : 1 ∉ S := by
    intro h1S
    have hne : 1 ≠ n := ne_of_lt hn1
    have hsub : ({1, n} : Finset ℕ) ⊆ S := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h1S
      · exact hnS
    have hle : ∑ m ∈ ({1, n} : Finset ℕ), (1 : ℚ) / m ≤ ∑ m ∈ S, (1 : ℚ) / m :=
      sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => by positivity)
    rw [sum_pair hne, hS_sum] at hle
    have hn_pos : (0 : ℚ) < (1 : ℚ) / n := by
      have : (0 : ℚ) < n := by exact_mod_cast (lt_trans zero_lt_one hn1)
      positivity
    have h1 : (1 : ℚ) / ((1 : ℕ) : ℚ) = 1 := by norm_num
    linarith
  refine ⟨insert 2 (S.image (2 * ·)), ?_, ?_, ?_⟩
  · intro x hx
    simp only [mem_insert, mem_image] at hx
    rw [mem_Icc]
    rcases hx with rfl | ⟨m, hmS, rfl⟩
    · omega
    · have hm := mem_Icc.mp (hS_sub hmS)
      omega
  · exact mem_insert_of_mem (mem_image_of_mem (2 * ·) hnS)
  · have h2_not_mem : 2 ∉ S.image (2 * ·) := by
      simp only [mem_image, not_exists, not_and]
      intro m hmS hm2
      have : m = 1 := by omega
      exact h1_not_mem (this ▸ hmS)
    have hinj : Function.Injective (2 * · : ℕ → ℕ) := by
      intro a b h
      dsimp at h
      omega
    rw [sum_insert h2_not_mem, sum_image (fun a _ b _ h => hinj h)]
    have h_factor : ∀ m ∈ S, (1 : ℚ) / ↑(2 * m) = (1 / 2 : ℚ) * ((1 : ℚ) / m) := by
      intro m _
      push_cast
      ring
    rw [sum_congr rfl h_factor, ← mul_sum, hS_sum]
    ring

end Challenge.Erdos292
