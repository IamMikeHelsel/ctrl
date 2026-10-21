import Mathlib.Tactic
/-! Five-prime arbitrary-family representation. This adapts the source pattern
in Research/CoveringFamily.even_smooth_representation without source edits. -/
noncomputable section
namespace M02Representation
abbrev Exponents := ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ
def modulus (x : Exponents) : ℕ :=
  2^(x.1.1.1+1)*3^x.1.1.2*5^x.1.2.1*7^x.1.2.2*11^x.2

theorem even_smooth_representation (m : ℕ) (hmin : 4≤m) (hp : (m+1).Prime)
    (hsmooth : ∃ a b c d e : ℕ, m=2^a*3^b*5^c*7^d*11^e) :
    ∃ x : Exponents, modulus x=m := by
  obtain ⟨a,b,c,d,e,hm⟩ := hsmooth
  have ha : 0<a := by
    by_contra hn
    have ha0 : a=0 := by omega
    have hodd : m%2=1 := by
      rw [hm,ha0]
      simp [Nat.mul_mod,Nat.pow_mod]
    have hprime := hp.eq_two_or_odd
    omega
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  exact ⟨(((k,b),(c,d)),e), by simpa only [modulus,Nat.succ_eq_add_one] using hm.symm⟩

/-- Choosing one exponent tuple per distinct modulus suffices for injectivity;
no arbitrary exponent bound or unproved global unique-factorization assertion. -/
theorem finite_family_representation (D : Finset ℕ)
    (hv : ∀ m∈D, 4≤m ∧ (m+1).Prime ∧
      ∃ a b c d e : ℕ, m=2^a*3^b*5^c*7^d*11^e) :
    ∃ T : Finset Exponents,
      (∀ m∈D, ∃ x∈T, modulus x=m) ∧
      (∀ x∈T, modulus x∈D) ∧ Set.InjOn modulus T := by
  classical
  have hex : ∀ m : D, ∃ x : Exponents, modulus x=m.val := by
    intro m
    have h := hv m.val m.property
    exact even_smooth_representation m.val h.1 h.2.1 h.2.2
  choose e he using hex
  let T : Finset Exponents := Finset.univ.image e
  have hrepr : ∀ x∈T, ∃ m : D, e m=x ∧ modulus x=m.val := by
    intro x hx
    obtain ⟨m,_,rfl⟩ := Finset.mem_image.mp hx
    exact ⟨m,rfl,he m⟩
  refine ⟨T,?_,?_,?_⟩
  · intro m hm
    exact ⟨e ⟨m,hm⟩,Finset.mem_image.mpr ⟨⟨m,hm⟩,Finset.mem_univ _,rfl⟩,he ⟨m,hm⟩⟩
  · intro x hx
    obtain ⟨m,_,heq⟩ := hrepr x hx
    rw [heq]
    exact m.property
  · intro x hx y hy hxy
    obtain ⟨m,rfl,hm⟩ := hrepr x hx
    obtain ⟨n,rfl,hn⟩ := hrepr y hy
    have hmn : m=n := Subtype.ext (hm.symm.trans (hxy.trans hn))
    exact congrArg e hmn

/-- Exact weight identity matching the five-factor geometric tail module. -/
theorem reciprocal_identity (x : Exponents) :
    (((1/2:ℝ)^(x.1.1.1+1)*(1/3:ℝ)^x.1.1.2)*
      ((1/5:ℝ)^x.1.2.1*(1/7:ℝ)^x.1.2.2))*(1/11:ℝ)^x.2 =
    1/(modulus x:ℝ) := by
  simp only [modulus,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,one_div,inv_pow,mul_inv_rev]
  ring

#print axioms even_smooth_representation
#print axioms finite_family_representation
#print axioms reciprocal_identity
end M02Representation
