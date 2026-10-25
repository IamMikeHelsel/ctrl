import Research.CoveringAssembly

/-! Arbitrary-family bridges for the seven-smooth exclusion. AI-assisted research. -/
namespace Research.CoveringFamily
open CoveringAssembly CoveringCapacity CoveringTail CoveringMass CoveringCRT

set_option maxRecDepth 4096

theorem modulus_mem_box (x : Exponents) (hx : x ∈ box) : modulus x ∈ exponentBox := by
  have hh : (x.1.1 < 10 ∧ x.1.2 < 7) ∧ (x.2.1 < 5 ∧ x.2.2 < 4) := by
    simpa only [box, Finset.mem_product, Finset.mem_range] using hx
  obtain ⟨⟨ha', hb'⟩, hc', hd'⟩ := hh
  simp only [exponentBox, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨x.1.1, ha', x.1.2, hb', x.2.1, hc', x.2.2, hd', rfl⟩

theorem admissible_mem_pool (x : Exponents) (hx : x ∈ box)
    (hmin : 4 ≤ modulus x) (hp : (modulus x + 1).Prime)
    (hprefix : modulus x ∉ ([4, 6, 10, 12] : List ℕ)) : modulus x ∈ pool := by
  rw [pool, List.mem_toFinset]
  apply List.mem_filter.mpr
  refine ⟨modulus_mem_box x hx, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨prime_passes_sieve _ hmin hp, hprefix⟩

theorem remainder_capacity (T : Finset Exponents) (U : Finset (Fin 60))
    (hinj : Set.InjOn modulus T)
    (hvalid : ∀ x ∈ T, 4 ≤ modulus x ∧ (modulus x + 1).Prime ∧
      modulus x ∉ ([4, 6, 10, 12] : List ℕ)) :
    (∑ x ∈ T.filter (· ∈ box), (Nat.gcd (modulus x) 60 : ℝ) *
        fiberCapacity U (Nat.gcd (modulus x) 60) / (modulus x : ℝ)) +
      60 * (∑ x ∈ T.filter (· ∉ box), 1 / (modulus x : ℝ)) ≤
        (scaledRemainderCapacity U : ℝ) / 1000 := by
  classical
  have hi :
      (∑ x ∈ T.filter (· ∈ box), (Nat.gcd (modulus x) 60 : ℝ) *
        fiberCapacity U (Nat.gcd (modulus x) 60) / (modulus x : ℝ)) ≤
      ∑ m ∈ pool, (m.gcd 60 : ℝ) * fiberCapacity U (m.gcd 60) / (m : ℝ) := by
    rw [← Finset.sum_image (f := fun m : ℕ => (m.gcd 60 : ℝ) *
      fiberCapacity U (m.gcd 60) / (m : ℝ))
      (s := T.filter (· ∈ box)) (g := modulus) (fun x hx y hy h =>
      hinj (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 h)]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hm
      have hv := hvalid x (Finset.mem_filter.mp hx).1
      exact admissible_mem_pool x (Finset.mem_filter.mp hx).2 hv.1 hv.2.1 hv.2.2
    · intro m hm _
      positivity
  have ht : (∑ x ∈ T.filter (· ∉ box), 1 / (modulus x : ℝ)) ≤
      632647 / 133358400 := by
    simp_rw [← weight_eq_reciprocal]
    apply finite_tail_bound
    exact Finset.disjoint_left.mpr (fun x hx hb => (Finset.mem_filter.mp hx).2 hb)
  have hc := pool_capacity_bound U
  linarith

/-- Convert a finite set of residues to their natural representatives. -/
def representatives (U : Finset (Fin 60)) : Finset ℕ := U.image Fin.val

theorem representatives_card (U : Finset (Fin 60)) : (representatives U).card = U.card := by
  exact Finset.card_image_of_injective _ Fin.val_injective

theorem representatives_lt (U : Finset (Fin 60)) : ∀ r ∈ representatives U, r < 60 := by
  intro r hr
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hr
  exact x.isLt

theorem representatives_fiber (U : Finset (Fin 60)) (g a : ℕ) (hg : 0 < g) :
    ((representatives U).filter (fun r => r % g = a % g)).card ≤ fiberCapacity U g := by
  have he : (representatives U).filter (fun r => r % g = a % g) =
      (U.filter (fun x => x.val % g = a % g)).image Fin.val := by
    ext r
    simp only [representatives, Finset.mem_filter, Finset.mem_image]
    aesop
  rw [he, Finset.card_image_of_injective _ Fin.val_injective]
  exact Finset.le_sup (s := Finset.range g) (f := fun r => (U.filter
    (fun x => x.val % g = r)).card) (Finset.mem_range.mpr (Nat.mod_lt a hg))

def lift (H : ℕ) (U : Finset (Fin 60)) : Finset ℕ :=
  (Finset.range H).filter (fun n : ℕ => n % 60 ∈ representatives U)

def hit (H m a : ℕ) : Finset ℕ := (Finset.range H).filter (fun n : ℕ => n % m = a % m)

theorem lift_size (H : ℕ) (hH : 60 ∣ H) (U : Finset (Fin 60)) :
    (lift H U).card = U.card * (H / 60) := by
  have he : H / 60 * 60 = H := Nat.div_mul_cancel hH
  have hc := lift_card 60 (H / 60) (by omega) (representatives U) (representatives_lt U)
  rw [he, representatives_card] at hc
  exact hc

theorem conditional_hit (H m a : ℕ) (h60 : 60 ∣ H) (hmH : m ∣ H)
    (hm : 0 < m) (U : Finset (Fin 60)) :
    ((lift H U ∩ hit H m a).card : ℝ) ≤
      (H : ℝ) / 60 * ((m.gcd 60 : ℝ) * fiberCapacity U (m.gcd 60) / (m : ℝ)) := by
  have hl : (60 : ℕ).lcm m ∣ H := Nat.lcm_dvd h60 hmH
  have he : H / (60 : ℕ).lcm m * (60 : ℕ).lcm m = H := Nat.div_mul_cancel hl
  have hc := conditional_class_card_le 60 m (H / (60 : ℕ).lcm m) (a % m)
    (by omega) hm (representatives U)
  rw [he] at hc
  have hset : lift H U ∩ hit H m a =
      (Finset.range H).filter (fun n : ℕ => n % 60 ∈ representatives U ∧ n % m = a % m) := by
    ext n
    simp only [lift, hit, Finset.mem_inter, Finset.mem_filter]
    tauto
  rw [← hset] at hc
  have hf := representatives_fiber U ((60 : ℕ).gcd m) (a % m) (Nat.gcd_pos_of_pos_left _ (by omega))
  have hc' : (lift H U ∩ hit H m a).card ≤
      fiberCapacity U (m.gcd 60) * (H / (60 : ℕ).lcm m) := by
    simpa only [Nat.gcd_comm] using hc.trans (Nat.mul_le_mul_right _ hf)
  have he' : (H / (60 : ℕ).lcm m : ℕ) * ((60 : ℕ).lcm m : ℝ) = (H : ℝ) := by exact_mod_cast he
  have hp : ((60 : ℕ).gcd m : ℝ) * ((60 : ℕ).lcm m : ℝ) = 60 * (m : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm 60 m
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hl' : (0 : ℝ) < (60 : ℕ).lcm m := by exact_mod_cast Nat.lcm_pos (by omega : 0 < 60) hm
  have hc'' : ((lift H U ∩ hit H m a).card : ℝ) ≤
      (fiberCapacity U (m.gcd 60) : ℝ) * (H / (60 : ℕ).lcm m : ℕ) := by exact_mod_cast hc'
  calc
    _ ≤ _ := hc''
    _ = _ := by
      rw [Nat.gcd_comm] at hp
      field_simp
      calc
        _ = (fiberCapacity U (m.gcd 60) : ℝ) * (H / (60 : ℕ).lcm m : ℕ) *
            ((m.gcd 60 : ℝ) * ((60 : ℕ).lcm m : ℝ)) := by rw [hp]; ring
        _ = (fiberCapacity U (m.gcd 60) : ℝ) *
            ((H / (60 : ℕ).lcm m : ℕ) * ((60 : ℕ).lcm m : ℝ)) * (m.gcd 60 : ℝ) := by ring
        _ = _ := by rw [he']


theorem unconditional_hit (H m a : ℕ) (hmH : m ∣ H) (hm : 0 < m)
    (U : Finset (Fin 60)) :
    ((lift H U ∩ hit H m a).card : ℝ) ≤ (H : ℝ) / (m : ℝ) := by
  have he : H / m * m = H := Nat.div_mul_cancel hmH
  have hc := lift_card m (H / m) hm {a % m} (by
    intro r hr
    have he : r = a % m := Finset.mem_singleton.mp hr
    rw [he]
    exact Nat.mod_lt a hm)
  have hsize : (hit H m a).card = H / m := by
    simpa only [he, Finset.mem_singleton, Finset.card_singleton, one_mul, hit] using hc
  have hi : (lift H U ∩ hit H m a).card ≤ H / m :=
    (Finset.card_le_card Finset.inter_subset_right).trans_eq hsize
  have hr : ((H / m : ℕ) : ℝ) = (H : ℝ) / (m : ℝ) := by
    apply (eq_div_iff (by exact_mod_cast hm.ne' : (m : ℝ) ≠ 0)).mpr
    exact_mod_cast he
  exact (by exact_mod_cast hi : ((lift H U ∩ hit H m a).card : ℝ) ≤
    ((H / m : ℕ) : ℝ)).trans_eq hr

theorem total_hit_bound (T : Finset Exponents) (r : ℕ → ℕ) (H : ℕ)
    (h60 : 60 ∣ H) (hdiv : ∀ x ∈ T, modulus x ∣ H) (U : Finset (Fin 60))
    (hinj : Set.InjOn modulus T)
    (hvalid : ∀ x ∈ T, 4 ≤ modulus x ∧ (modulus x + 1).Prime ∧
      modulus x ∉ ([4, 6, 10, 12] : List ℕ)) :
    (∑ x ∈ T, ((lift H U ∩ hit H (modulus x) (r (modulus x))).card : ℝ)) ≤
      (H : ℝ) / 60 * ((scaledRemainderCapacity U : ℝ) / 1000) := by
  classical
  have hi :
      (∑ x ∈ T.filter (· ∈ box),
        ((lift H U ∩ hit H (modulus x) (r (modulus x))).card : ℝ)) ≤
      (H : ℝ) / 60 * (∑ x ∈ T.filter (· ∈ box),
        ((modulus x).gcd 60 : ℝ) * fiberCapacity U ((modulus x).gcd 60) /
          (modulus x : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    exact conditional_hit H _ _ h60 (hdiv x (Finset.mem_filter.mp hx).1)
      (modulus_pos x) U
  have ht :
      (∑ x ∈ T.filter (· ∉ box),
        ((lift H U ∩ hit H (modulus x) (r (modulus x))).card : ℝ)) ≤
      (H : ℝ) * (∑ x ∈ T.filter (· ∉ box), 1 / (modulus x : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    simpa only [mul_one_div] using unconditional_hit H _ _
      (hdiv x (Finset.mem_filter.mp hx).1) (modulus_pos x) U
  have hs := Finset.sum_filter_add_sum_filter_not T (· ∈ box)
    (fun x => ((lift H U ∩ hit H (modulus x) (r (modulus x))).card : ℝ))
  have hrem := mul_le_mul_of_nonneg_left (remainder_capacity T U hinj hvalid)
    (by positivity : (0 : ℝ) ≤ H / 60)
  nlinarith

theorem uncovered_card_bound (S : Finset ℕ) (T : Finset Exponents)
    (A : Exponents → Finset ℕ) :
    S.card ≤ (S \ T.biUnion A).card + ∑ x ∈ T, (S ∩ A x).card := by
  have he := Finset.card_sdiff_add_card_inter S (T.biUnion A)
  have hb := Finset.card_biUnion_le (s := T) (t := fun x => S ∩ A x)
  have hi : S ∩ T.biUnion A = T.biUnion (fun x => S ∩ A x) := by
    ext n
    simp only [Finset.mem_inter, Finset.mem_biUnion]
    aesop
  rw [← hi] at hb
  omega

/-- Uniform period bound after normalizing the residue modulo four. -/
theorem normalized_gap (T : Finset Exponents) (r : ℕ → ℕ) (H : ℕ)
    (h60 : 60 ∣ H) (hdiv : ∀ x ∈ T, modulus x ∣ H)
    (hinj : Set.InjOn modulus T)
    (hvalid : ∀ x ∈ T, 4 ≤ modulus x ∧ (modulus x + 1).Prime)
    (hr4 : r 4 % 4 = 0) :
    (H : ℝ) * (57 / 10000) ≤
      (((Finset.range H).filter (fun n : ℕ => ∀ x ∈ T, n % modulus x ≠ r (modulus x) % modulus x)).card : ℝ) := by
  classical
  let U := survivors ⟨r 6 % 6, Nat.mod_lt _ (by omega)⟩
    ⟨r 10 % 10, Nat.mod_lt _ (by omega)⟩ ⟨r 12 % 12, Nat.mod_lt _ (by omega)⟩
  let R := T.filter (fun x => modulus x ∉ ([4, 6, 10, 12] : List ℕ))
  let G := lift H U \ R.biUnion (fun x => hit H (modulus x) (r (modulus x)))
  have hb := total_hit_bound R r H h60
    (fun x hx => hdiv x (Finset.mem_filter.mp hx).1) U
    (fun x hx y hy he => hinj (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 he)
    (fun x hx => ⟨(hvalid x (Finset.mem_filter.mp hx).1).1,
      (hvalid x (Finset.mem_filter.mp hx).1).2, (Finset.mem_filter.mp hx).2⟩)
  have hc := uncovered_card_bound (lift H U) R (fun x => hit H (modulus x) (r (modulus x)))
  have hc' : ((lift H U).card : ℝ) ≤ (G.card : ℝ) +
      ∑ x ∈ R, ((lift H U ∩ hit H (modulus x) (r (modulus x))).card : ℝ) := by
    exact_mod_cast hc
  have hsize : ((lift H U).card : ℝ) = (U.card : ℝ) * ((H : ℝ) / 60) := by
    rw [lift_size H h60 U, Nat.cast_mul]
    have he := Nat.div_mul_cancel h60
    have hf : ((H / 60 : ℕ) : ℝ) = (H : ℝ) / 60 := by
      apply (eq_div_iff (by norm_num : (60 : ℝ) ≠ 0)).mpr
      exact_mod_cast he
    rw [hf]
  have hcert : (scaledRemainderCapacity U : ℝ) + 342 ≤ 1000 * (U.card : ℝ) := by
    exact_mod_cast seven_smooth_capacity_certificate
      ⟨r 6 % 6, Nat.mod_lt _ (by omega)⟩ ⟨r 10 % 10, Nat.mod_lt _ (by omega)⟩
      ⟨r 12 % 12, Nat.mod_lt _ (by omega)⟩
  have hg : (H : ℝ) * (57 / 10000) ≤ (G.card : ℝ) := by
    have hscaled := mul_le_mul_of_nonneg_left hcert (by positivity : (0 : ℝ) ≤ H / 60000)
    rw [hsize] at hc'
    nlinarith
  have hsubset : G ⊆ (Finset.range H).filter
      (fun n : ℕ => ∀ x ∈ T, n % modulus x ≠ r (modulus x) % modulus x) := by
    intro n hn
    obtain ⟨hnU, hnR⟩ := Finset.mem_sdiff.mp hn
    obtain ⟨hnH, hnU⟩ := Finset.mem_filter.mp hnU
    obtain ⟨z, hz, hzn⟩ := Finset.mem_image.mp hnU
    have hz' : z.val % 4 ≠ 0 ∧ z.val % 6 ≠ r 6 % 6 ∧
        z.val % 10 ≠ r 10 % 10 ∧ z.val % 12 ≠ r 12 % 12 := by
      simpa only [U, survivors, Finset.mem_filter, Finset.mem_univ, true_and] using hz
    apply Finset.mem_filter.mpr
    refine ⟨hnH, ?_⟩
    intro x hx he
    by_cases hp : modulus x ∈ ([4, 6, 10, 12] : List ℕ)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with hp | hp | hp | hp
      · have hmod := Nat.mod_mod_of_dvd n (by norm_num : 4 ∣ 60)
        rw [← hzn] at hmod
        rw [hp, hr4] at he
        exact hz'.1 (hmod.trans he)
      · have hmod := Nat.mod_mod_of_dvd n (by norm_num : 6 ∣ 60)
        rw [← hzn] at hmod
        rw [hp] at he
        exact hz'.2.1 (hmod.trans he)
      · have hmod := Nat.mod_mod_of_dvd n (by norm_num : 10 ∣ 60)
        rw [← hzn] at hmod
        rw [hp] at he
        exact hz'.2.2.1 (hmod.trans he)
      · have hmod := Nat.mod_mod_of_dvd n (by norm_num : 12 ∣ 60)
        rw [← hzn] at hmod
        rw [hp] at he
        exact hz'.2.2.2 (hmod.trans he)
    · exact hnR (Finset.mem_biUnion.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hp⟩,
        Finset.mem_filter.mpr ⟨hnH, he⟩⟩)
  exact hg.trans (by exact_mod_cast Finset.card_le_card hsubset)


/-- Arbitrary integer residues: a complete period beginning at the selected
residue modulo four contains at least 57/10000 uncovered points. -/
theorem integer_period_gap (T : Finset Exponents) (r : ℕ → ℤ) (H : ℕ)
    (h60 : 60 ∣ H) (hdiv : ∀ x ∈ T, modulus x ∣ H)
    (hinj : Set.InjOn modulus T)
    (hvalid : ∀ x ∈ T, 4 ≤ modulus x ∧ (modulus x + 1).Prime) :
    (H : ℝ) * (57 / 10000) ≤
      (((Finset.range H).filter (fun n : ℕ => ∀ x ∈ T,
        ((n : ℤ) + r 4) % (modulus x : ℤ) ≠ r (modulus x) % (modulus x : ℤ))).card : ℝ) := by
  classical
  let s : ℕ → ℕ := fun m => ((r m - r 4) % (m : ℤ)).toNat
  have hs4 : s 4 % 4 = 0 := by simp [s]
  have hconv (n m : ℕ) (hm : 0 < m) :
      n % m = s m ↔ ((n : ℤ) + r 4) % (m : ℤ) = r m % (m : ℤ) := by
    have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
    have hs : ((s m : ℕ) : ℤ) = (r m - r 4) % (m : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ hm')
    constructor
    · intro he
      have he' : (n : ℤ) % (m : ℤ) = (r m - r 4) % (m : ℤ) := by
        rw [← hs, ← Int.natCast_emod]
        exact_mod_cast he
      calc
        _ = ((n : ℤ) % (m : ℤ) + r 4) % (m : ℤ) := (Int.emod_add_emod _ _ _).symm
        _ = ((r m - r 4) % (m : ℤ) + r 4) % (m : ℤ) := by rw [he']
        _ = (r m - r 4 + r 4) % (m : ℤ) := Int.emod_add_emod _ _ _
        _ = _ := by rw [sub_add_cancel]
    · intro he
      have hz := congrArg (fun z : ℤ => (z - r 4) % (m : ℤ)) he
      simp only [Int.emod_sub_emod, add_sub_cancel_right] at hz
      rw [← hs, ← Int.natCast_emod] at hz
      exact_mod_cast hz
  have hslt (m : ℕ) (hm : 0 < m) : s m < m := by
    have hm' : (0 : ℤ) < m := by exact_mod_cast hm
    have hs : ((s m : ℕ) : ℤ) = (r m - r 4) % (m : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ hm'.ne')
    have hh := Int.emod_lt_of_pos (r m - r 4) hm'
    rw [← hs] at hh
    exact_mod_cast hh
  have hg := normalized_gap T s H h60 hdiv hinj hvalid hs4
  have he : (Finset.range H).filter (fun n : ℕ => ∀ x ∈ T,
      n % modulus x ≠ s (modulus x) % modulus x) =
      (Finset.range H).filter (fun n : ℕ => ∀ x ∈ T,
        ((n : ℤ) + r 4) % (modulus x : ℤ) ≠ r (modulus x) % (modulus x : ℤ)) := by
    apply Finset.filter_congr
    intro n hn
    apply forall_congr'
    intro x
    apply forall_congr'
    intro hx
    rw [Nat.mod_eq_of_lt (hslt _ (modulus_pos x))]
    exact not_congr (hconv n (modulus x) (modulus_pos x))
  rw [he] at hg
  exact hg

/-- Positivity of the two-exponent follows from primality of the successor;
there is no parity restriction hidden in the final theorem. -/
theorem even_smooth_representation (m : ℕ) (hmin : 4 ≤ m) (hp : (m + 1).Prime)
    (hsmooth : ∃ a b c d : ℕ, m = 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) :
    ∃ x : Exponents, modulus x = m := by
  obtain ⟨a, b, c, d, hm⟩ := hsmooth
  have ha : 0 < a := by
    by_contra hn
    have ha0 : a = 0 := by omega
    have hodd : m % 2 = 1 := by
      rw [hm, ha0]
      simp [Nat.mul_mod, Nat.pow_mod]
    have hprime := hp.eq_two_or_odd
    omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  exact ⟨((k, b), (c, d)), by simpa only [modulus, Nat.succ_eq_add_one] using hm.symm⟩

/-- The complete seven-smooth restriction, with a uniform period-density gap.
D is any finite set of distinct moduli, all smooth exponents are unbounded,
and the residues are arbitrary integers. No capacity bound is assumed. -/
theorem seven_smooth_period_gap (D : Finset ℕ) (r : ℕ → ℤ) (H : ℕ)
    (h60 : 60 ∣ H) (hdiv : ∀ m ∈ D, m ∣ H)
    (hvalid : ∀ m ∈ D, 4 ≤ m ∧ (m + 1).Prime ∧
      ∃ a b c d : ℕ, m = 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) :
    (H : ℝ) * (57 / 10000) ≤
      (((Finset.range H).filter (fun n : ℕ => ∀ m ∈ D,
        ((n : ℤ) + r 4) % (m : ℤ) ≠ r m % (m : ℤ))).card : ℝ) := by
  classical
  have hex : ∀ m : D, ∃ x : Exponents, modulus x = m.val := by
    intro m
    have hv := hvalid m.val m.property
    exact even_smooth_representation m.val hv.1 hv.2.1 hv.2.2
  choose e he using hex
  let T : Finset Exponents := Finset.univ.image e
  have hrepr : ∀ x ∈ T, ∃ m : D, e m = x ∧ modulus x = m.val := by
    intro x hx
    obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨m, rfl, he m⟩
  have hinj : Set.InjOn modulus T := by
    intro x hx y hy hxy
    obtain ⟨m, rfl, hm⟩ := hrepr x hx
    obtain ⟨n, rfl, hn⟩ := hrepr y hy
    have hmn : m = n := Subtype.ext (hm.symm.trans (hxy.trans hn))
    exact congrArg e hmn
  have hg := integer_period_gap T r H h60 (by
    intro x hx
    obtain ⟨m, _, hm⟩ := hrepr x hx
    rw [hm]
    exact hdiv m.val m.property) hinj (by
    intro x hx
    obtain ⟨m, _, hm⟩ := hrepr x hx
    rw [hm]
    exact ⟨(hvalid m.val m.property).1, (hvalid m.val m.property).2.1⟩)
  have heq : (Finset.range H).filter (fun n : ℕ => ∀ x ∈ T,
      ((n : ℤ) + r 4) % (modulus x : ℤ) ≠ r (modulus x) % (modulus x : ℤ)) =
      (Finset.range H).filter (fun n : ℕ => ∀ m ∈ D,
      ((n : ℤ) + r 4) % (m : ℤ) ≠ r m % (m : ℤ)) := by
    apply Finset.filter_congr
    intro n hn
    constructor
    · intro h m hm
      have hh := h (e ⟨m, hm⟩) (Finset.mem_image.mpr ⟨⟨m, hm⟩, Finset.mem_univ _, rfl⟩)
      simpa only [he] using hh
    · intro h x hx
      obtain ⟨m, _, hm⟩ := hrepr x hx
      simpa only [hm] using h m.val m.property
  rwa [heq] at hg

/-- In particular, no finite distinct covering can use only such moduli. -/
theorem seven_smooth_not_cover (D : Finset ℕ) (r : ℕ → ℤ)
    (hvalid : ∀ m ∈ D, 4 ≤ m ∧ (m + 1).Prime ∧
      ∃ a b c d : ℕ, m = 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) :
    ∃ n : ℤ, ∀ m ∈ D, n % (m : ℤ) ≠ r m % (m : ℤ) := by
  classical
  let H := 60 * ∏ m ∈ D, m
  have hH : 0 < H := Nat.mul_pos (by omega) (Finset.prod_pos (by
    intro m hm
    have := (hvalid m hm).1
    omega))
  have hg := seven_smooth_period_gap D r H (dvd_mul_right _ _) (by
    intro m hm
    exact (Finset.dvd_prod_of_mem id hm).trans (dvd_mul_left _ _)) hvalid
  have hc : 0 < ((Finset.range H).filter (fun n : ℕ => ∀ m ∈ D,
      ((n : ℤ) + r 4) % (m : ℤ) ≠ r m % (m : ℤ))).card := by
    have hH' : (0 : ℝ) < H := by exact_mod_cast hH
    have hp : (0 : ℝ) < H * (57 / 10000) := mul_pos hH' (by norm_num)
    exact_mod_cast hp.trans_le hg
  obtain ⟨n, hn⟩ := Finset.card_pos.mp hc
  exact ⟨(n : ℤ) + r 4, (Finset.mem_filter.mp hn).2⟩

#print axioms seven_smooth_period_gap
#print axioms seven_smooth_not_cover

end Research.CoveringFamily
