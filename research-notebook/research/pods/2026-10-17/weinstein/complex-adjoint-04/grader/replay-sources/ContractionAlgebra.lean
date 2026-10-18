import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace GUContraction

variable {I A : Type*} [Fintype I] [DecidableEq I] [Ring A] [Algebra ℝ A]

structure PairSymmetries (r : I → I → I → I → ℝ) : Prop where
  skew1 : ∀ a b c d, r a b c d = -r b a c d
  skew2 : ∀ a b c d, r a b c d = -r a b d c
  exchange : ∀ a b c d, r a b c d = r c d a b

structure Curvature (r : I → I → I → I → ℝ) : Prop extends PairSymmetries r where
  bianchi : ∀ a b c d, r a b c d - r a c b d + r a d b c = 0

def traceR (r : I → I → I → I → ℝ) (ε : I → ℝ) : ℝ :=
  ∑ a, ∑ b, ε a * ε b * r a b a b

def total (r : I → I → I → I → ℝ) (g : I → A) : A :=
  ∑ a, ∑ b, ∑ c, ∑ d, r a b c d • (g a * g b * g c * g d)

def crossed (r : I → I → I → I → ℝ) (g : I → A) : A :=
  ∑ a, ∑ b, ∑ c, ∑ d, r a b c d • (g a * g c * g b * g d)

def cycled (r : I → I → I → I → ℝ) (g : I → A) : A :=
  ∑ a, ∑ b, ∑ c, ∑ d, r a b c d • (g a * g c * g d * g b)

def diagonalContract (r : I → I → I → I → ℝ) (ε : I → ℝ) (g : I → A) : A :=
  ∑ a, ∑ b, ∑ c, (r a b c b * ε b) • (g a * g c)

theorem symmetric_contraction (ε : I → ℝ) (g : I → A)
    (hg : ∀ a b, g a * g b + g b * g a = (if a=b then 2*ε a else 0) • (1:A))
    (t : I → I → ℝ) (ht : ∀ a b, t a b = t b a) :
    (∑ a, ∑ b, t a b • (g a * g b)) = (∑ a, t a a * ε a) • (1:A) := by
  have hs : (∑ a, ∑ b, t a b • (g b * g a)) = ∑ a, ∑ b, t a b • (g a * g b) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [ht b a]
  have htwo : (2:ℝ) • (∑ a, ∑ b, t a b • (g a * g b)) =
      (2:ℝ) • ((∑ a, t a a * ε a) • (1:A)) := by
    calc
      _ = (∑ a, ∑ b, t a b • (g a * g b + g b * g a)) := by
        simp only [smul_add, Finset.sum_add_distrib, hs, two_smul]
      _ = (∑ a, ∑ b, t a b • ((if a=b then 2*ε a else 0) • (1:A))) := by
        simp_rw [hg]
      _ = _ := by
        simp only [ite_smul, zero_smul, smul_ite, smul_zero, Finset.sum_ite_eq,
          Finset.mem_univ, ite_true, smul_smul]
        simp only [← Finset.sum_smul]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
  have hh := congrArg (fun x:A => (1/2:ℝ) • x) htwo
  norm_num [smul_smul] at hh
  convert hh using 1
  congr 1
  ring

theorem diagonalContract_eq (r : I → I → I → I → ℝ) (hr : PairSymmetries r)
    (ε : I → ℝ) (g : I → A)
    (hg : ∀ a b, g a * g b + g b * g a = (if a=b then 2*ε a else 0) • (1:A)) :
    diagonalContract r ε g = traceR r ε • (1:A) := by
  unfold diagonalContract traceR
  rw [Finset.sum_comm]
  have hh (b:I) : (∑ a, ∑ c, (r a b c b * ε b) • (g a * g c)) =
      (∑ a, r a b a b * ε b * ε a) • (1:A) :=
    symmetric_contraction ε g hg (fun a c => r a b c b * ε b)
      (fun a c => by rw [hr.exchange a b c b])
  simp_rw [hh]
  simp only [← Finset.sum_smul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem word_swap (ε : I → ℝ) (g : I → A)
    (hg : ∀ a b, g a * g b + g b * g a = (if a=b then 2*ε a else 0) • (1:A))
    (a b c d : I) :
    g a * g c * g b * g d = -(g a * g b * g c * g d) +
      if b=c then (2*ε b) • (g a * g d) else 0 := by
  have h : g a * g b * g c * g d + g a * g c * g b * g d =
      if b=c then (2*ε b) • (g a * g d) else 0 := by
    simpa [mul_add, add_mul, mul_assoc, mul_smul_comm, smul_mul_assoc,
      ite_smul] using congrArg (fun x:A => g a * x * g d) (hg b c)
  calc
    _ = -(g a * g b * g c * g d) +
        (g a * g b * g c * g d + g a * g c * g b * g d) := by abel
    _ = _ := by rw [h]

theorem crossed_eq (r : I → I → I → I → ℝ) (hr : PairSymmetries r)
    (ε : I → ℝ) (g : I → A)
    (hg : ∀ a b, g a * g b + g b * g a = (if a=b then 2*ε a else 0) • (1:A)) :
    crossed r g = -total r g - (2:ℝ) • diagonalContract r ε g := by
  have hs : crossed r g = ∑ a, ∑ b, ∑ c, ∑ d, r a b c d •
      (-(g a * g b * g c * g d) + if b=c then (2*ε b) • (g a * g d) else 0) := by
    unfold crossed
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro c _
    apply Finset.sum_congr rfl; intro d _
    rw [word_swap ε g hg a b c d]
  rw [hs]
  simp only [smul_add, smul_neg, smul_ite, smul_zero, Finset.sum_add_distrib,
    Finset.sum_neg_distrib]
  change -total r g + _ = _
  have hc : (∑ a, ∑ b, ∑ c, ∑ d,
      if b=c then r a b c d • ((2*ε b) • (g a * g d)) else 0) =
      -(2:ℝ) • diagonalContract r ε g := by
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    unfold diagonalContract
    simp only [Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro d _
    rw [hr.skew2 a b b d]
    congr 1
    ring
  rw [hc]
  module

theorem word_last_swap (ε : I → ℝ) (g : I → A)
    (hg : ∀ a b, g a * g b + g b * g a = (if a=b then 2*ε a else 0) • (1:A))
    (a b c d : I) :
    g a * g c * g d * g b = -(g a * g c * g b * g d) +
      if b=d then (2*ε b) • (g a * g c) else 0 := by
  have h : g a * g c * g b * g d + g a * g c * g d * g b =
      if b=d then (2*ε b) • (g a * g c) else 0 := by
    simpa [mul_add, add_mul, mul_assoc, mul_smul_comm, smul_mul_assoc,
      ite_smul] using congrArg (fun x:A => g a * g c * x) (hg b d)
  calc
    _ = -(g a * g c * g b * g d) +
        (g a * g c * g b * g d + g a * g c * g d * g b) := by abel
    _ = _ := by rw [h]

theorem cycled_eq (r : I → I → I → I → ℝ)
    (ε : I → ℝ) (g : I → A)
    (hg : ∀ a b, g a * g b + g b * g a = (if a=b then 2*ε a else 0) • (1:A)) :
    cycled r g = -crossed r g + (2:ℝ) • diagonalContract r ε g := by
  have hs : cycled r g = ∑ a, ∑ b, ∑ c, ∑ d, r a b c d •
      (-(g a * g c * g b * g d) + if b=d then (2*ε b) • (g a * g c) else 0) := by
    unfold cycled
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro c _
    apply Finset.sum_congr rfl; intro d _
    rw [word_last_swap ε g hg a b c d]
  rw [hs]
  simp only [smul_add, smul_neg, smul_ite, smul_zero, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  change -crossed r g + _ = _
  congr 1
  unfold diagonalContract
  simp only [Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  congr 1
  ring

theorem bianchi_sum (r : I → I → I → I → ℝ) (hr : Curvature r) (g : I → A) :
    total r g - crossed r g + cycled r g = 0 := by
  have h : (∑ a, ∑ b, ∑ c, ∑ d,
      (r a b c d-r a c b d+r a d b c) • (g a * g b * g c * g d)) = (0:A) := by
    simp only [hr.bianchi, zero_smul, Finset.sum_const_zero]
  simp only [sub_smul, add_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib] at h
  have hcross : (∑ a, ∑ b, ∑ c, ∑ d, r a c b d • (g a * g b * g c * g d)) = crossed r g := by
    unfold crossed
    apply Finset.sum_congr rfl; intro a _
    exact Finset.sum_comm
  have hcycle : (∑ a, ∑ b, ∑ c, ∑ d, r a d b c • (g a * g b * g c * g d)) = cycled r g := by
    unfold cycled
    apply Finset.sum_congr rfl; intro a _
    calc
      _ = ∑ b, ∑ d, ∑ c, r a d b c • (g a * g b * g c * g d) := by
        apply Finset.sum_congr rfl; intro b _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hcross, hcycle] at h
  exact h

theorem total_contraction (r : I → I → I → I → ℝ) (hr : Curvature r)
    (ε : I → ℝ) (g : I → A)
    (hg : ∀ a b, g a * g b + g b * g a = (if a=b then 2*ε a else 0) • (1:A)) :
    total r g = (-2 * traceR r ε) • (1:A) := by
  have h := bianchi_sum r hr g
  calc
    total r g = (1/3:ℝ) • (total r g-crossed r g+cycled r g) -
        (2:ℝ) • diagonalContract r ε g := by
      rw [cycled_eq r ε g hg, crossed_eq r hr.toPairSymmetries ε g hg]
      module
    _ = _ := by
      rw [h, smul_zero, zero_sub, diagonalContract_eq r hr.toPairSymmetries ε g hg]
      module

section Sorted
variable [LinearOrder I]

def pairs : Finset (I × I) := Finset.univ.filter (fun p => p.1<p.2)

theorem sum_sorted (f : I → I → A) (hs : ∀ a b, f a b=f b a)
    (hd : ∀ a, f a a=0) :
    (∑ a, ∑ b, f a b) = (2:ℝ) • ∑ p ∈ pairs (I:=I), f p.1 p.2 := by
  have hp (a b:I) : f a b = (if a<b then f a b else 0)+(if b<a then f a b else 0) := by
    rcases lt_trichotomy a b with h|h|h
    · simp [h, not_lt.mpr (le_of_lt h)]
    · subst b; simp [hd]
    · simp [h, not_lt.mpr (le_of_lt h)]
  have hswap : (∑ a, ∑ b, if b<a then f a b else 0) =
      ∑ a, ∑ b, if a<b then f a b else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    rw [hs b a]
  calc
    _ = ∑ a, ∑ b, ((if a<b then f a b else 0)+(if b<a then f a b else 0)) := by
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      exact hp a b
    _ = (2:ℝ) • (∑ a, ∑ b, if a<b then f a b else 0) := by
      simp only [Finset.sum_add_distrib, hswap, two_smul]
    _ = _ := by
      simp [pairs, Finset.sum_filter, Fintype.sum_prod_type]

def sortedWord (r : I → I → I → I → ℝ) (g : I → A) : A :=
  ∑ p ∈ pairs (I:=I), ∑ q ∈ pairs (I:=I),
    r p.1 p.2 q.1 q.2 • (g p.1 * g p.2 * g q.1 * g q.2)

def sortedK (r : I → I → I → I → ℝ) (g : I → A) : A :=
  ∑ p ∈ pairs (I:=I), ∑ q ∈ pairs (I:=I),
    r p.1 p.2 q.1 q.2 • (g p.1 * g p.2 * g q.1 * g q.2 +
      g q.1 * g q.2 * g p.1 * g p.2)

theorem sortedK_eq_two (r : I → I → I → I → ℝ) (hr : PairSymmetries r) (g : I → A) :
    sortedK r g = (2:ℝ) • sortedWord r g := by
  have hs : (∑ p ∈ pairs (I:=I), ∑ q ∈ pairs (I:=I),
      r p.1 p.2 q.1 q.2 • (g q.1 * g q.2 * g p.1 * g p.2)) = sortedWord r g := by
    unfold sortedWord
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    rw [hr.exchange]
  unfold sortedK
  simp only [smul_add, Finset.sum_add_distrib, hs]
  change sortedWord r g + sortedWord r g = _
  module

theorem term_swap1 (r : I → I → I → I → ℝ) (hr : PairSymmetries r)
    (ε : I → ℝ) (g : I → A)
    (hg : ∀ a b, g a * g b + g b * g a = (if a=b then 2*ε a else 0) • (1:A))
    (a b c d:I) :
    r a b c d • (g a*g b*g c*g d) = r b a c d • (g b*g a*g c*g d) := by
  by_cases hab : a=b
  · subst b; rfl
  · have hs : g a*g b=-(g b*g a) := by
      apply eq_neg_of_add_eq_zero_left
      simpa [hab] using hg a b
    rw [hr.skew1 a b c d, hs]
    simp

theorem term_swap2 (r : I → I → I → I → ℝ) (hr : PairSymmetries r)
    (ε : I → ℝ) (g : I → A)
    (hg : ∀ a b, g a * g b + g b * g a = (if a=b then 2*ε a else 0) • (1:A))
    (a b c d:I) :
    r a b c d • (g a*g b*g c*g d) = r a b d c • (g a*g b*g d*g c) := by
  by_cases hcd : c=d
  · subst d; rfl
  · have hs : g c*g d=-(g d*g c) := by
      apply eq_neg_of_add_eq_zero_left
      simpa [hcd] using hg c d
    simp only [mul_assoc]
    rw [hr.skew2 a b c d, hs]
    simp

theorem total_eq_four_sorted (r : I → I → I → I → ℝ) (hr : PairSymmetries r)
    (ε : I → ℝ) (g : I → A)
    (hg : ∀ a b, g a * g b + g b * g a = (if a=b then 2*ε a else 0) • (1:A)) :
    total r g = (4:ℝ) • sortedWord r g := by
  have hz1 (a c d:I) : r a a c d=0 := by have h:=hr.skew1 a a c d; linarith
  have hz2 (a b c:I) : r a b c c=0 := by have h:=hr.skew2 a b c c; linarith
  have hs1 (a b:I) : (∑ c, ∑ d, r a b c d • (g a*g b*g c*g d)) =
      ∑ c, ∑ d, r b a c d • (g b*g a*g c*g d) := by
    apply Finset.sum_congr rfl; intro c _
    apply Finset.sum_congr rfl; intro d _
    exact term_swap1 r hr ε g hg a b c d
  have ho := sum_sorted (fun a b => ∑ c, ∑ d, r a b c d • (g a*g b*g c*g d)) hs1
    (fun a => by simp [hz1])
  calc
    total r g = (2:ℝ) • ∑ p ∈ pairs (I:=I), ∑ c, ∑ d,
        r p.1 p.2 c d • (g p.1*g p.2*g c*g d) := ho
    _ = (2:ℝ) • ∑ p ∈ pairs (I:=I), (2:ℝ) • ∑ q ∈ pairs (I:=I),
        r p.1 p.2 q.1 q.2 • (g p.1*g p.2*g q.1*g q.2) := by
      congr 1
      apply Finset.sum_congr rfl; intro p _
      exact sum_sorted (fun c d => r p.1 p.2 c d • (g p.1*g p.2*g c*g d))
        (term_swap2 r hr ε g hg p.1 p.2) (fun c => by simp [hz2])
    _ = _ := by
      rw [← Finset.smul_sum, smul_smul]
      norm_num [sortedWord]

theorem normalization_bridge (r : I → I → I → I → ℝ) (hr : PairSymmetries r)
    (ε : I → ℝ) (g : I → A)
    (hg : ∀ a b, g a * g b + g b * g a = (if a=b then 2*ε a else 0) • (1:A)) :
    total r g = (2:ℝ) • sortedK r g := by
  rw [total_eq_four_sorted r hr ε g hg, sortedK_eq_two r hr g]
  module

theorem sorted_contraction (r : I → I → I → I → ℝ) (hr : Curvature r)
    (ε : I → ℝ) (g : I → A)
    (hg : ∀ a b, g a * g b + g b * g a = (if a=b then 2*ε a else 0) • (1:A)) :
    sortedK r g = (-traceR r ε) • (1:A) := by
  have ht := total_contraction r hr ε g hg
  rw [normalization_bridge r hr.toPairSymmetries ε g hg] at ht
  calc
    sortedK r g = (1/2:ℝ) • ((2:ℝ) • sortedK r g) := by module
    _ = (1/2:ℝ) • ((-2 * traceR r ε) • (1:A)) := congrArg _ ht
    _ = _ := by module

end Sorted
end GUContraction
