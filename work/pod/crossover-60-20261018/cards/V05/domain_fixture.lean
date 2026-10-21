import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

noncomputable section
namespace V05Domain
abbrev V := EuclideanSpace ℝ (Fin 3)
def p (i : Fin 3) : V := WithLp.toLp 2 ![if i.val = 1 then 1 else 0, if i.val = 2 then 1 else 0, 0]
def q (i : Fin 3) : V := WithLp.toLp 2 ![if i.val = 1 then 1 else 0, if i.val = 2 then 1 else 0, 1]
def shift : V := WithLp.toLp 2 ![10,0,0]
def qa (i : Fin 3) : V := p i
def qb (i : Fin 3) : V := q i + shift

lemma cross_source (i j : Fin 3) : dist (p i) (q j) ≤ 7/4 := by
  rw [dist_eq_norm]
  have h : ‖p i-q j‖^2 ≤ 3 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    fin_cases i <;> fin_cases j <;> norm_num [p,q,Fin.sum_univ_succ,PiLp.sub_apply]
  have hn := norm_nonneg (p i-q j)
  nlinarith

lemma cross_target (i j : Fin 3) : 9 ≤ dist (qa i) (qb j) := by
  rw [dist_eq_norm]
  have h := PiLp.norm_apply_le (qa i-qb j) (0 : Fin 3)
  fin_cases i <;> fin_cases j <;> norm_num [qa,qb,p,q,shift, PiLp.sub_apply, PiLp.add_apply] at h ⊢ <;> linarith

lemma incompatible (T : V → V) (hT : Isometry T) (i j : Fin 3)
    (ha : dist (T (p i)) (qa i) < 1) : 1 ≤ dist (T (q j)) (qb j) := by
  have h1 := dist_triangle (qa i) (T (p i)) (qb j)
  have h2 := dist_triangle (T (p i)) (T (q j)) (qb j)
  have hd := hT.dist_eq (p i) (q j)
  have hs := cross_source i j
  have ht := cross_target i j
  rw [dist_comm (qa i) (T (p i))] at h1
  linarith

def tls (T : V → V) : ℝ :=
  (∑ i : Fin 3, min ((dist (T (p i)) (qa i))^2) 1) +
  (∑ i : Fin 3, min ((dist (T (q i)) (qb i))^2) 1)

lemma cap_nonneg (x : ℝ) : 0 ≤ min (x^2) 1 := le_min (sq_nonneg x) (by norm_num)
lemma cap_one (x : ℝ) (hx : 1 ≤ x) : min (x^2) 1 = 1 := by
  apply min_eq_right
  nlinarith

lemma tls_lower (T : V → V) (hT : Isometry T) : 3 ≤ tls T := by
  by_cases ha : ∃ i : Fin 3, dist (T (p i)) (qa i) < 1
  · obtain ⟨i, hi⟩ := ha
    have hb : ∀ j : Fin 3, min ((dist (T (q j)) (qb j))^2) 1 = 1 :=
      fun j => cap_one _ (incompatible T hT i j hi)
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

lemma shift_norm : ‖shift‖^2 = 100 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  norm_num [shift, Fin.sum_univ_succ]

lemma identity_attains : tls id = 3 := by
  have hd (j : Fin 3) : dist (q j) (qb j)^2 = 100 := by
    rw [dist_eq_norm]
    have he : q j - qb j = -shift := by simp [qb]
    rw [he, norm_neg, shift_norm]
  simp [tls,qa,hd]

def translated (x : V) : V := x + shift

lemma translated_attains : tls translated = 3 := by
  have hd (j : Fin 3) : dist (translated (p j)) (qa j)^2 = 100 := by
    rw [dist_eq_norm]
    have he : translated (p j) - qa j = shift := by simp [translated,qa]
    rw [he, shift_norm]
  have hz (j : Fin 3) : dist (translated (q j)) (qb j) = 0 := by simp [translated,qb]
  simp [tls,hd,hz]

lemma translated_isometry : Isometry translated := by
  apply Isometry.of_dist_eq
  intro x y
  simp [translated,dist_eq_norm]

lemma distinct_poses : id (0 : V) ≠ translated 0 := by
  intro h
  have h0 := congrArg (fun v : V => v 0) h
  norm_num [translated,shift] at h0

#print axioms cross_source
#print axioms cross_target
#print axioms incompatible
#print axioms tls_lower
#print axioms identity_attains
#print axioms translated_attains
#print axioms translated_isometry
#print axioms distinct_poses
end V05Domain
