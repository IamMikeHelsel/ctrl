import domain_fixture
noncomputable section
namespace V05Domain

lemma cross_scaled_incompatible (s : ℝ) (hs : 0 ≤ s) (hu : s ≤ 4)
    (T : V → V) (hT : ∀ x y, dist (T x) (T y) = s * dist x y)
    (i j : Fin 3) (ha : dist (T (p i)) (qa i) < 1) :
    1 ≤ dist (T (q j)) (qb j) := by
  have h1 := dist_triangle (qa i) (T (p i)) (qb j)
  have h2 := dist_triangle (T (p i)) (T (q j)) (qb j)
  rw [dist_comm (qa i) (T (p i))] at h1
  rw [hT] at h2
  have hs0 := dist_nonneg (x := p i) (y := q j)
  have hsb := cross_source i j
  have htb := cross_target i j
  nlinarith

lemma scaled_small_lower (s : ℝ) (hs : 0 ≤ s) (hu : s ≤ 4)
    (T : V → V) (hT : ∀ x y, dist (T x) (T y) = s * dist x y) :
    3 ≤ tls T := by
  by_cases ha : ∃ i : Fin 3, dist (T (p i)) (qa i) < 1
  · obtain ⟨i, hi⟩ := ha
    have hb : ∀ j : Fin 3, min ((dist (T (q j)) (qb j))^2) 1 = 1 :=
      fun j => cap_one _ (cross_scaled_incompatible s hs hu T hT i j hi)
    have hn := Finset.sum_nonneg (s := Finset.univ)
      (fun (j : Fin 3) _ => cap_nonneg (dist (T (p j)) (qa j)))
    simp only [tls, hb, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at *
    norm_num at *
    linarith
  · push_neg at ha
    have hb : ∀ j : Fin 3, min ((dist (T (p j)) (qa j))^2) 1 = 1 :=
      fun j => cap_one _ (ha j)
    have hn := Finset.sum_nonneg (s := Finset.univ)
      (fun (j : Fin 3) _ => cap_nonneg (dist (T (q j)) (qb j)))
    simp only [tls, hb, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at *
    norm_num at *
    linarith

lemma within_p (i j : Fin 3) (hij : i ≠ j) :
    1 ≤ dist (p i) (p j) ∧ dist (p i) (p j) ≤ 2 := by
  rw [dist_eq_norm]
  have h : 1 ≤ ‖p i-p j‖^2 ∧ ‖p i-p j‖^2 ≤ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    fin_cases i <;> fin_cases j <;> simp_all [p,Fin.sum_univ_succ,PiLp.sub_apply] <;> norm_num
  have hn := norm_nonneg (p i-p j)
  constructor <;> nlinarith

lemma within_q (i j : Fin 3) : dist (q i) (q j) = dist (p i) (p j) := by
  rw [dist_eq_norm,dist_eq_norm]
  congr 1
  ext k
  fin_cases k <;> simp [p,q,PiLp.sub_apply]

lemma cap_pair (a b : ℝ) (h : a < 1 → 1 ≤ b) : 1 ≤ min (a^2) 1 + min (b^2) 1 := by
  by_cases ha : a < 1
  · rw [cap_one b (h ha)]
    have := cap_nonneg a
    linarith
  · rw [cap_one a (le_of_not_gt ha)]
    have := cap_nonneg b
    linarith

lemma three_pair_bound (r : Fin 3 → ℝ)
    (h : ∀ i j, i ≠ j → r i < 1 → 1 ≤ r j) :
    (2:ℝ) ≤ ∑ i, min ((r i)^2) 1 := by
  have hn0 := cap_nonneg (r 0)
  have hn1 := cap_nonneg (r 1)
  have hn2 := cap_nonneg (r 2)
  by_cases h0 : r 0 < 1
  · have h1 := cap_one (r 1) (h 0 1 (by decide) h0)
    have h2 := cap_one (r 2) (h 0 2 (by decide) h0)
    simp [Fin.sum_univ_succ, h1, h2]
    linarith
  · have he0 := cap_one (r 0) (le_of_not_gt h0)
    by_cases h1 : r 1 < 1
    · have he2 := cap_one (r 2) (h 1 2 (by decide) h1)
      simp [Fin.sum_univ_succ, he0, he2]
      linarith
    · have he1 := cap_one (r 1) (le_of_not_gt h1)
      simp [Fin.sum_univ_succ, he0, he1]
      linarith

lemma large_incompatible (s : ℝ) (hs : 4 < s) (T : V → V)
    (hT : ∀ x y, dist (T x) (T y) = s * dist x y)
    (x y a b : V) (hxy : 1 ≤ dist x y) (hab : dist a b ≤ 2)
    (ha : dist (T x) a < 1) : 1 ≤ dist (T y) b := by
  have h1 := dist_triangle (T x) a (T y)
  have h2 := dist_triangle a b (T y)
  rw [hT] at h1
  rw [dist_comm b (T y)] at h2
  nlinarith

lemma scaled_large_lower (s : ℝ) (hs : 4 < s) (T : V → V)
    (hT : ∀ x y, dist (T x) (T y) = s * dist x y) : 4 ≤ tls T := by
  have ha := three_pair_bound (fun i => dist (T (p i)) (qa i)) (by
    intro i j hij hi
    exact large_incompatible s hs T hT _ _ _ _ (within_p i j hij).1 (within_p i j hij).2 hi)
  have hb := three_pair_bound (fun i => dist (T (q i)) (qb i)) (by
    intro i j hij hi
    apply large_incompatible s hs T hT _ _ _ _ _ _ hi
    · rw [within_q]; exact (within_p i j hij).1
    · simp only [qb,dist_add_right,within_q]; exact (within_p i j hij).2)
  unfold tls
  linarith

lemma similarity_tls_lower (s : ℝ) (hs : 0 ≤ s) (T : V → V)
    (hT : ∀ x y, dist (T x) (T y) = s * dist x y) : 3 ≤ tls T := by
  rcases le_or_gt s 4 with h | h
  · exact scaled_small_lower s hs h T hT
  · have := scaled_large_lower s h T hT
    linarith

#print axioms cross_scaled_incompatible
#print axioms scaled_small_lower
#print axioms within_p
#print axioms within_q
#print axioms three_pair_bound
#print axioms scaled_large_lower
#print axioms similarity_tls_lower
end V05Domain
