import Mathlib.LinearAlgebra.ExteriorPower.HodgeStar
import Mathlib.Tactic

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Module exteriorPower
namespace GUHodgeBridge
abbrev V := Fin 14 → ℝ
abbrev E (k : ℕ) := ⋀[ℝ]^k V
abbrev Ix (k : ℕ) := Set.powersetCard (Fin 14) k

def b : Basis (Fin 14) ℝ V := Pi.basisFun ℝ (Fin 14)
def e (k : ℕ) : Basis (Ix k) ℝ (E k) := b.exteriorPower k

def d (i : Fin 14) : ℝˣ := if i.val < 7 then 1 else -1

def metricEquiv : V ≃ₗ[ℝ] Module.Dual ℝ V :=
  b.repr.trans (b.dualBasis.unitsSMul d).repr.symm

def B : LinearMap.BilinForm ℝ V := metricEquiv.toLinearMap

theorem B_bijective : Function.Bijective B := metricEquiv.bijective

theorem B_basis (i : Fin 14) : B (b i) = (d i : ℝ) • b.dualBasis i := by
  simp [B, metricEquiv, Basis.unitsSMul_apply, Units.smul_def]

theorem B_basis_basis (i j : Fin 14) :
    B (b i) (b j) = if i = j then (d i : ℝ) else 0 := by
  rw [B_basis]
  simp only [LinearMap.smul_apply, Basis.dualBasis_apply_self, smul_eq_mul]
  split_ifs <;> simp_all

theorem finrank_V : Module.finrank ℝ V = 14 := by simp

instance topUnique : Unique (Ix (Module.finrank ℝ V)) where
  default := ⟨Finset.univ, by simp⟩
  uniq s := Subtype.ext (Finset.eq_univ_of_card _ (by simp))

def vol : E (Module.finrank ℝ V) ≃ₗ[ℝ] ℝ :=
  (e _).equivFun.trans (LinearEquiv.funUnique _ ℝ ℝ)

theorem vol_top : vol b.topVector = 1 := by
  change (e _).repr b.topVector default = 1
  change ((b.exteriorPower _).repr ((b.exteriorPower _) _)) default = 1
  simp only [Basis.repr_self]
  rw [Subsingleton.elim (⟨Finset.univ, by simp⟩ : Ix (finrank ℝ V)) default]
  exact Finsupp.single_eq_same

def subsetIndexEquiv (k : ℕ) : Ix k ≃ Fin (Nat.choose 14 k) :=
  Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card, Set.powersetCard.card]; simp)

def coordinates (k : ℕ) : E k ≃ₗ[ℝ] (Fin (Nat.choose 14 k) → ℝ) :=
  ((e k).reindex (subsetIndexEquiv k)).equivFun

def mu {k : ℕ} (I : Ix k) : ℝ := ∏ i ∈ I.val, (d i : ℝ)
def eps {k : ℕ} (I : Ix k) : ℝ := (Set.powersetCard.sign I : ℤ)

def complement {k l : ℕ} (h : k+l=14) : Ix k ≃ Ix l :=
  Set.powersetCard.compl (by simpa [Nat.add_comm] using h)

def H {k l : ℕ} (h : k+l=14) : E k ≃ₗ[ℝ] E l :=
  exteriorPower.hodgeStar B B_bijective vol (h.trans finrank_V.symm)

theorem H_pairing {k l : ℕ} (h : k+l=14) (x : E k) (y : E l) :
    B.exteriorPower l (H h x) y =
      exteriorPower.wedgePairing vol (h.trans finrank_V.symm) x y := by
  have hh : B.exteriorPower l (H h x) =
      exteriorPower.wedgePairing vol (h.trans finrank_V.symm) x := by
    simp [H, exteriorPower.hodgeStar]
  exact congrArg (fun f : Module.Dual ℝ (E l) => f y) hh

theorem mu_ordered {k : ℕ} (I : Ix k) :
    (∏ j : Fin k, (d (Set.powersetCard.ofFinEmbEquiv.symm I j) : ℝ)) = mu I := by
  unfold mu
  rw [← Finset.prod_coe_sort I.val (fun i => (d i : ℝ))]
  exact Fintype.prod_equiv (Set.powersetCard.orderIsoOfFin I).toEquiv
    (fun j => (d (Set.powersetCard.ofFinEmbEquiv.symm I j) : ℝ))
    (fun j => (d j : ℝ)) (by intro j; rfl)

theorem Bext_basis {k : ℕ} (I : Ix k) :
    B.exteriorPower k (e k I) = mu I • (e k).dualBasis I := by
  change exteriorPower.pairingDual ℝ V k
    (exteriorPower.map k B (b.exteriorPower k I)) = _
  rw [exteriorPower.basis_apply, exteriorPower.map_apply_ιMulti_family]
  have hc : B ∘ b = fun i => (d i : ℝ) • b.dualBasis i := by
    funext i
    exact B_basis i
  rw [hc]
  change exteriorPower.pairingDual ℝ V k
    (exteriorPower.ιMulti ℝ k (fun j =>
      (d (Set.powersetCard.ofFinEmbEquiv.symm I j) : ℝ) •
      b.dualBasis (Set.powersetCard.ofFinEmbEquiv.symm I j))) = _
  rw [AlternatingMap.map_smul_univ, mu_ordered, map_smul]
  congr 1
  simpa only [e, exteriorPower.basis_apply, exteriorPower.ιMulti_family, Function.comp_def] using
    exteriorPower.pairingDual_apply_dualBasis_exteriorPower k b I


theorem mu_sq {k : ℕ} (I : Ix k) : mu I * mu I = 1 := by
  unfold mu
  rw [← Finset.prod_mul_distrib]
  have hd (i : Fin 14) : (d i : ℝ) * (d i : ℝ) = 1 := by
    simp [d]; split_ifs <;> norm_num
  simp_rw [hd]
  simp

theorem wedge_basis {k l : ℕ} (h : k+l=14) (I : Ix k) :
    exteriorPower.wedgePairing vol (h.trans finrank_V.symm) (e k I) =
      eps I • (e l).dualBasis (complement h I) := by
  rw [exteriorPower.wedgePairing_eq_apply_topVector_smul vol _ b, vol_top, one_smul]
  simp only [e, LinearEquiv.coe_coe, LinearEquiv.trans_apply, Basis.repr_self,
    Basis.repr_symm_single, Basis.groupSMul_apply, Pi.smul_apply', one_smul,
    Basis.reindex_apply]
  simp only [eps, complement, Set.powersetCard.compl_symm]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.smul_apply, Units.smul_def, zsmul_eq_mul, smul_eq_mul]

theorem H_basis {k l : ℕ} (h : k+l=14) (I : Ix k) :
    H h (e k I) = (eps I * mu (complement h I)) • e l (complement h I) := by
  apply (B.bijective_exteriorPower l B_bijective).injective
  have hp : B.exteriorPower l (H h (e k I)) =
      exteriorPower.wedgePairing vol (h.trans finrank_V.symm) (e k I) := by
    exact LinearMap.ext (fun y => H_pairing h _ y)
  rw [hp, wedge_basis, map_smul, Bext_basis, smul_smul]
  rw [mul_assoc, mu_sq, mul_one]


theorem mu_univ : (∏ i : Fin 14, (d i : ℝ)) = -1 := by
  norm_num [d, Fin.prod_univ_succ]

theorem mu_complement_product {k l : ℕ} (h : k+l=14) (I : Ix k) :
    mu I * mu (complement h I) = -1 := by
  unfold mu complement
  rw [Set.powersetCard.coe_compl, Finset.prod_mul_prod_compl, mu_univ]

theorem mu_complement {k l : ℕ} (h : k+l=14) (I : Ix k) :
    mu (complement h I) = -mu I := by
  calc
    _ = (mu I * mu I) * mu (complement h I) := by rw [mu_sq, one_mul]
    _ = mu I * (mu I * mu (complement h I)) := mul_assoc _ _ _
    _ = -mu I := by rw [mu_complement_product]; ring

theorem eps_sq {k : ℕ} (I : Ix k) : eps I * eps I = 1 := by
  unfold eps
  exact_mod_cast Int.units_coe_mul_self (Set.powersetCard.sign I)

theorem complement_twice {k l : ℕ} (h : k+l=14) (I : Ix k) :
    complement (show l+k=14 by omega) (complement h I) = I := by
  apply Subtype.ext
  simp [complement]

theorem wedge_basis_swap (I : Ix 2) (J : Ix 12) :
    exteriorPower.wedge ℝ V 2 12 (e 2 I) (e 12 J) =
      exteriorPower.wedge ℝ V 12 2 (e 12 J) (e 2 I) := by
  apply Subtype.ext
  change (e 2 I : ExteriorAlgebra ℝ V) * (e 12 J : ExteriorAlgebra ℝ V) =
    (e 12 J : ExteriorAlgebra ℝ V) * (e 2 I : ExteriorAlgebra ℝ V)
  simp only [e, exteriorPower.basis_apply, exteriorPower.ιMulti_family_apply_coe]
  change ExteriorAlgebra.ιMulti ℝ 2 (b ∘ Set.powersetCard.ofFinEmbEquiv.symm I) *
    ExteriorAlgebra.ιMulti ℝ 12 (b ∘ Set.powersetCard.ofFinEmbEquiv.symm J) =
    ExteriorAlgebra.ιMulti ℝ 12 (b ∘ Set.powersetCard.ofFinEmbEquiv.symm J) *
    ExteriorAlgebra.ιMulti ℝ 2 (b ∘ Set.powersetCard.ofFinEmbEquiv.symm I)
  have hs : (-1 : ℤˣ) ^ (12*2) = 1 := by decide
  simpa only [hs, one_smul] using ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm ℝ
    (b ∘ Set.powersetCard.ofFinEmbEquiv.symm I)
    (b ∘ Set.powersetCard.ofFinEmbEquiv.symm J)

theorem wedgePairing_basis_swap (I : Ix 2) (J : Ix 12) :
    exteriorPower.wedgePairing vol (show 2+12=finrank ℝ V by rw [finrank_V]) (e 2 I) (e 12 J) =
    exteriorPower.wedgePairing vol (show 12+2=finrank ℝ V by rw [finrank_V]) (e 12 J) (e 2 I) := by
  unfold exteriorPower.wedgePairing
  simp only [LinearMap.compr₂_apply]
  congr 1
  exact wedge_basis_swap I J

theorem eps_complement_2 (I : Ix 2) : eps (complement (by decide : 2+12=14) I) = eps I := by
  have hw := wedgePairing_basis_swap I (complement (by decide : 2+12=14) I)
  rw [wedge_basis (by decide : 2+12=14), wedge_basis (by decide : 12+2=14)] at hw
  simp only [complement_twice, LinearMap.smul_apply, Basis.dualBasis_apply_self,
    ite_true, smul_eq_mul, mul_one] at hw
  exact hw.symm

theorem H_square_basis (I : Ix 2) :
    H (by decide : 12+2=14) (H (by decide : 2+12=14) (e 2 I)) = -(e 2 I) := by
  rw [H_basis, map_smul, H_basis, complement_twice, eps_complement_2, smul_smul]
  have hc : (eps I * mu (complement (by decide : 2+12=14) I)) * (eps I * mu I) = -1 := by
    calc
      _ = (eps I * eps I) * (mu I * mu (complement (by decide : 2+12=14) I)) := by ring
      _ = -1 := by rw [eps_sq, mu_complement_product]; norm_num
  rw [hc, neg_one_smul]

theorem H_square (x : E 2) :
    H (by decide : 12+2=14) (H (by decide : 2+12=14) x) = -x := by
  have hh : (H (by decide : 12+2=14)).toLinearMap.comp
      (H (by decide : 2+12=14)).toLinearMap = -LinearMap.id := by
    apply (e 2).ext
    exact H_square_basis
  exact LinearMap.congr_fun hh x


/-- The alpha-wedge-star convention, proved below to have its defining pairing. -/
def S {k l : ℕ} (h : k+l=14) : E k →ₗ[ℝ] E l := -(H h).toLinearMap

theorem S_basis {k l : ℕ} (h : k+l=14) (I : Ix k) :
    S h (e k I) = (eps I * mu I) • e l (complement h I) := by
  rw [S, LinearMap.neg_apply, LinearEquiv.coe_coe, H_basis,
    mu_complement, mul_neg]
  exact (congrArg Neg.neg (neg_smul (eps I * mu I) (e l (complement h I)))).trans (neg_neg _)

theorem H_eq_neg_S {k l : ℕ} (h : k+l=14) : (H h).toLinearMap = -S h := by
  exact (neg_neg (H h).toLinearMap).symm

theorem S_pairing {k l : ℕ} (h : k+l=14) (x y : E k) :
    exteriorPower.wedgePairing vol (h.trans finrank_V.symm) x (S h y) =
      B.exteriorPower k x y := by
  have hh : (exteriorPower.wedgePairing vol (h.trans finrank_V.symm)).compl₂ (S h) =
      B.exteriorPower k := by
    apply (e k).ext
    intro I
    apply (e k).ext
    intro J
    change exteriorPower.wedgePairing vol (h.trans finrank_V.symm) (e k I) (S h (e k J)) =
      B.exteriorPower k (e k I) (e k J)
    rw [S_basis, wedge_basis h I, Bext_basis]
    simp only [LinearMap.smul_apply, map_smul, Basis.dualBasis_apply_self, smul_eq_mul]
    by_cases hij : I = J
    · subst J
      simp only [ite_true]
      calc
        eps I * mu I * (eps I * 1) = (eps I * eps I) * mu I := by ring
        _ = mu I * 1 := by rw [eps_sq]; ring
    · have hc : complement h J ≠ complement h I := fun he => hij ((complement h).injective he).symm
      simp [Ne.symm hij, hc]
  exact LinearMap.congr_fun (LinearMap.congr_fun hh x) y

theorem S_square (x : E 2) :
    S (by decide : 12+2=14) (S (by decide : 2+12=14) x) = -x := by
  simp only [S, LinearMap.neg_apply, LinearEquiv.coe_coe, map_neg, neg_neg, H_square]

/-- The coefficient array has the same index type as SwerveCoefficients.star2. -/
def star2 : Fin (Nat.choose 14 12) → Fin (Nat.choose 14 2) → ℝ :=
  fun o i => coordinates 12 (H (by decide : 2+12=14)
    ((e 2).reindex (subsetIndexEquiv 2) i)) o

theorem star2_represents (x : E 2) (o : Fin (Nat.choose 14 12)) :
    coordinates 12 (H (by decide : 2+12=14) x) o =
      ∑ i, star2 o i * coordinates 2 x i := by
  conv_lhs => rw [← ((e 2).reindex (subsetIndexEquiv 2)).sum_repr x]
  simp only [map_sum, map_smul, star2, coordinates, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Basis.equivFun_apply]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem star2_signed_complement (o : Fin (Nat.choose 14 12)) (i : Fin (Nat.choose 14 2)) :
    star2 o i =
      if o = subsetIndexEquiv 12 (complement (by decide : 2+12=14) ((subsetIndexEquiv 2).symm i))
      then eps ((subsetIndexEquiv 2).symm i) *
        mu (complement (by decide : 2+12=14) ((subsetIndexEquiv 2).symm i)) else 0 := by
  simp only [star2, Basis.reindex_apply, H_basis, coordinates, map_smul,
    Basis.equivFun_apply, Basis.repr_reindex_apply, Pi.smul_apply,
    Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
  by_cases ho : o = subsetIndexEquiv 12
      (complement (by decide : 2+12=14) ((subsetIndexEquiv 2).symm i))
  · subst o
    simp
  · have hn : complement (by decide : 2+12=14) ((subsetIndexEquiv 2).symm i) ≠
        (subsetIndexEquiv 12).symm o := by
      intro he
      apply ho
      simpa using (congrArg (subsetIndexEquiv 12) he).symm
    simp [ho, hn]


/-- Signed-complement formula extended to every form by linearity. -/
theorem H_expansion {k l : ℕ} (h : k+l=14) (x : E k) :
    H h x = ∑ I : Ix k, (e k).repr x I •
      ((eps I * mu (complement h I)) • e l (complement h I)) := by
  conv_lhs => rw [← (e k).sum_repr x]
  simp only [map_sum, map_smul, H_basis]

theorem H_reverse_square (y : E 12) :
    H (by decide : 2+12=14) (H (by decide : 12+2=14) y) = -y := by
  obtain ⟨x, rfl⟩ := (H (by decide : 2+12=14)).surjective y
  rw [H_square, map_neg]

end GUHodgeBridge
