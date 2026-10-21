import Challenge.Erdos939

open Erdos939 Nat Finset

namespace Challenge.Erdos939

lemma full_pow {r a n : ℕ} (hn : r ≤ n) : r.Full (a ^ n) := by
  intro p hp
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ a ^ n := Nat.dvd_of_mem_primeFactors hp
  have hp_a : p ∣ a := hp_prime.dvd_of_dvd_pow hp_dvd
  exact dvd_trans (pow_dvd_pow p hn) (pow_dvd_pow_of_dvd hp_a n)

lemma full_mul {r a b : ℕ} (ha : r.Full a) (hb : r.Full b) : r.Full (a * b) := by
  intro p hp
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ a * b := Nat.dvd_of_mem_primeFactors hp
  have hne0 : a * b ≠ 0 := (Nat.mem_primeFactors.mp hp).2.2
  rcases hp_prime.dvd_mul.mp hp_dvd with hpa | hpb
  · exact dvd_mul_of_dvd_left
      (ha p (Nat.mem_primeFactors.mpr ⟨hp_prime, hpa, left_ne_zero_of_mul hne0⟩)) b
  · exact dvd_mul_of_dvd_right
      (hb p (Nat.mem_primeFactors.mpr ⟨hp_prime, hpb, right_ne_zero_of_mul hne0⟩)) a

lemma binom6_identity (X B : ℕ) (hBX : B ≤ X) :
    (X - B) ^ 6 + (12 * X ^ 5 * B + (40 * X ^ 3 * B ^ 3 + 12 * X * B ^ 5)) = (X + B) ^ 6 := by
  obtain ⟨D, rfl⟩ := Nat.exists_eq_add_of_le hBX
  rw [Nat.add_sub_cancel_left]
  ring

/-- The fixed base `Y = 2^4 * 3^5 * 5^6 = 60,750,000`. -/
def Y : ℕ := 60750000

/-- The parameter `m(k) = 30 * (k + 1) + 1`. -/
def mParam (k : ℕ) : ℕ := 30 * (k + 1) + 1

/-- The parameter `X(k) = m(k)^6`. -/
def XParam (k : ℕ) : ℕ := (mParam k) ^ 6

def s1 (k : ℕ) : ℕ := (XParam k - Y) ^ 6
def s2 (k : ℕ) : ℕ := 12 * (XParam k) ^ 5 * Y
def s3 (k : ℕ) : ℕ := 40 * (XParam k) ^ 3 * Y ^ 3
def s4 (k : ℕ) : ℕ := 12 * (XParam k) * Y ^ 5

lemma XParam_ge (k : ℕ) : 887503681 ≤ XParam k := by
  have hm : 31 ≤ mParam k := by
    dsimp [mParam]
    omega
  calc
    887503681 = 31 ^ 6 := by norm_num
    _ ≤ (mParam k) ^ 6 := Nat.pow_le_pow_left hm 6

lemma Y_lt_XParam (k : ℕ) : Y < XParam k := by
  have hX := XParam_ge k
  dsimp [Y]
  omega

lemma s1_pos (k : ℕ) : 0 < s1 k :=
  Nat.pow_pos (Nat.sub_pos_of_lt (Y_lt_XParam k))

lemma s_chain (k : ℕ) : 0 < s4 k ∧ s4 k < s3 k ∧ s3 k < s2 k := by
  have hX := XParam_ge k
  have hXY : Y < XParam k := Y_lt_XParam k
  have hY_pos : 0 < Y := by decide
  have hX_pos : 0 < XParam k := lt_trans hY_pos hXY
  have hs4_pos : 0 < s4 k := by
    dsimp [s4]
    positivity
  have h_sq1 : 3 * Y ^ 2 < 10 * (XParam k) ^ 2 := by
    calc
      3 * Y ^ 2 < 10 * 887503681 ^ 2 := by norm_num [Y]
      _ ≤ 10 * (XParam k) ^ 2 := Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left hX 2)
  have h_sq2 : 10 * Y ^ 2 < 3 * (XParam k) ^ 2 := by
    calc
      10 * Y ^ 2 < 3 * 887503681 ^ 2 := by norm_num [Y]
      _ ≤ 3 * (XParam k) ^ 2 := Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hX 2)
  have hs43 : s4 k < s3 k := by
    have hpos : 0 < 4 * XParam k * Y ^ 3 := by positivity
    calc
      s4 k = (4 * XParam k * Y ^ 3) * (3 * Y ^ 2) := by dsimp [s4]; ring
      _ < (4 * XParam k * Y ^ 3) * (10 * (XParam k) ^ 2) :=
        Nat.mul_lt_mul_of_pos_left h_sq1 hpos
      _ = s3 k := by dsimp [s3]; ring
  have hs32 : s3 k < s2 k := by
    have hpos : 0 < 4 * (XParam k) ^ 3 * Y := by positivity
    calc
      s3 k = (4 * (XParam k) ^ 3 * Y) * (10 * Y ^ 2) := by dsimp [s3]; ring
      _ < (4 * (XParam k) ^ 3 * Y) * (3 * (XParam k) ^ 2) :=
        Nat.mul_lt_mul_of_pos_left h_sq2 hpos
      _ = s2 k := by dsimp [s2]; ring
  exact ⟨hs4_pos, hs43, hs32⟩

lemma s1_mod_two (k : ℕ) : s1 k % 2 = 1 := by
  have hm_odd : Odd (mParam k) := ⟨15 * (k + 1), by dsimp [mParam]; ring⟩
  have hX_odd : Odd (XParam k) := hm_odd.pow
  obtain ⟨u, hu⟩ := hX_odd
  have hYX : Y ≤ XParam k := le_of_lt (Y_lt_XParam k)
  have h_sub_odd : Odd (XParam k - Y) := by
    refine ⟨u - 30375000, ?_⟩
    dsimp [Y] at hYX ⊢
    omega
  exact Nat.odd_iff.mp h_sub_odd.pow

lemma s2_mod_two (k : ℕ) : s2 k % 2 = 0 := by
  have h : s2 k = 2 * (6 * (XParam k) ^ 5 * Y) := by dsimp [s2]; ring
  rw [h, Nat.mul_mod_right]

lemma s3_mod_two (k : ℕ) : s3 k % 2 = 0 := by
  have h : s3 k = 2 * (20 * (XParam k) ^ 3 * Y ^ 3) := by dsimp [s3]; ring
  rw [h, Nat.mul_mod_right]

lemma s4_mod_two (k : ℕ) : s4 k % 2 = 0 := by
  have h : s4 k = 2 * (6 * (XParam k) * Y ^ 5) := by dsimp [s4]; ring
  rw [h, Nat.mul_mod_right]

lemma s_sum_eq (k : ℕ) : s1 k + (s2 k + (s3 k + s4 k)) = (XParam k + Y) ^ 6 :=
  binom6_identity (XParam k) Y (le_of_lt (Y_lt_XParam k))

lemma c2_eq : 12 * Y = 30 ^ 6 := by norm_num [Y]
lemma c3_eq : 40 * Y ^ 3 = 2 ^ 15 * 3 ^ 15 * 5 ^ 19 := by norm_num [Y]
lemma c4_eq : 12 * Y ^ 5 = 2 ^ 22 * 3 ^ 26 * 5 ^ 30 := by norm_num [Y]
lemma dvd_Y_30_pow : Y ∣ 30 ^ 6 := ⟨12, by norm_num [Y]⟩
lemma dvd_30_Y : 30 ∣ Y := ⟨2025000, by norm_num [Y]⟩

lemma s2_eq_pow (k : ℕ) : s2 k = (30 * (mParam k) ^ 5) ^ 6 := by
  calc
    s2 k = (12 * Y) * (XParam k) ^ 5 := by dsimp [s2]; ring
    _ = 30 ^ 6 * ((mParam k) ^ 6) ^ 5 := by rw [c2_eq, XParam]
    _ = (30 * (mParam k) ^ 5) ^ 6 := by ring

lemma s3_eq_pow (k : ℕ) : s3 k = 2 ^ 15 * 3 ^ 15 * 5 ^ 19 * ((mParam k) ^ 3) ^ 6 := by
  calc
    s3 k = (40 * Y ^ 3) * (XParam k) ^ 3 := by dsimp [s3]; ring
    _ = 2 ^ 15 * 3 ^ 15 * 5 ^ 19 * ((mParam k) ^ 6) ^ 3 := by rw [c3_eq, XParam]
    _ = 2 ^ 15 * 3 ^ 15 * 5 ^ 19 * ((mParam k) ^ 3) ^ 6 := by ring

lemma s4_eq_pow (k : ℕ) : s4 k = 2 ^ 22 * 3 ^ 26 * 5 ^ 30 * (mParam k) ^ 6 := by
  calc
    s4 k = (12 * Y ^ 5) * XParam k := by dsimp [s4]; ring
    _ = 2 ^ 22 * 3 ^ 26 * 5 ^ 30 * (mParam k) ^ 6 := by rw [c4_eq, XParam]

lemma s12_coprime (k : ℕ) : Nat.Coprime (s1 k) (s2 k) := by
  have hm30 : Nat.Coprime (mParam k) 30 := by
    have hm_eq : mParam k = 1 + (k + 1) * 30 := by dsimp [mParam]; ring
    rw [hm_eq, Nat.coprime_add_mul_right_left]
    exact Nat.coprime_one_left 30
  have hX30 : Nat.Coprime (XParam k) (30 ^ 6) := hm30.pow 6 6
  have hXY : Nat.Coprime (XParam k) Y := hX30.of_dvd_right dvd_Y_30_pow
  have hYX : Y ≤ XParam k := le_of_lt (Y_lt_XParam k)
  obtain ⟨D, hD⟩ := Nat.exists_eq_add_of_le hYX
  have h_sub_eq : XParam k - Y = D := by
    rw [hD, Nat.add_sub_cancel_left]
  have hDY : Nat.Coprime D Y := by
    have hYD : Nat.Coprime (Y + D) Y := hD ▸ hXY
    exact Nat.coprime_self_add_left.mp hYD
  have h_sub_Y : Nat.Coprime (XParam k - Y) Y := h_sub_eq ▸ hDY
  have h_sub_30 : Nat.Coprime (XParam k - Y) 30 :=
    h_sub_Y.of_dvd_right dvd_30_Y
  have h_sub_X : Nat.Coprime (XParam k - Y) (XParam k) := by
    rw [h_sub_eq, hD]
    exact Nat.coprime_add_self_right.mpr hDY
  have h_sub_m5 : Nat.Coprime (XParam k - Y) ((mParam k) ^ 5) :=
    h_sub_X.of_dvd_right ⟨mParam k, by dsimp [XParam]; ring⟩
  have h_sub_base : Nat.Coprime (XParam k - Y) (30 * (mParam k) ^ 5) :=
    h_sub_30.mul_right h_sub_m5
  rw [s1, s2_eq_pow]
  exact h_sub_base.pow 6 6

lemma s1_full (k : ℕ) : (6 : ℕ).Full (s1 k) := by
  rw [s1]
  exact full_pow (le_refl 6)

lemma s2_full (k : ℕ) : (6 : ℕ).Full (s2 k) := by
  rw [s2_eq_pow]
  exact full_pow (le_refl 6)

lemma s3_full (k : ℕ) : (6 : ℕ).Full (s3 k) := by
  rw [s3_eq_pow]
  exact full_mul (full_mul (full_mul (full_pow (by omega)) (full_pow (by omega)))
    (full_pow (by omega))) (full_pow (le_refl 6))

lemma s4_full (k : ℕ) : (6 : ℕ).Full (s4 k) := by
  rw [s4_eq_pow]
  exact full_mul (full_mul (full_mul (full_pow (by omega)) (full_pow (by omega)))
    (full_pow (by omega))) (full_pow (le_refl 6))

attribute [irreducible] s1 s2 s3 s4

lemma card_and_sum_four {a b c d : ℕ}
    (ha : a % 2 = 1) (hb : b % 2 = 0) (hc : c % 2 = 0) (hd : d % 2 = 0)
    (hdc : d < c) (hcb : c < b) :
    ({a, b, c, d} : Finset ℕ).card = 4 ∧
      ∑ s ∈ ({a, b, c, d} : Finset ℕ), s = a + (b + (c + d)) := by
  have h12 : a ≠ b := fun h => by omega
  have h13 : a ≠ c := fun h => by omega
  have h14 : a ≠ d := fun h => by omega
  have h23 : b ≠ c := ne_of_gt hcb
  have h24 : b ≠ d := ne_of_gt (lt_trans hdc hcb)
  have h34 : c ≠ d := ne_of_gt hdc
  have hnot1 : a ∉ ({b, c, d} : Finset ℕ) := by simp [h12, h13, h14]
  have hnot2 : b ∉ ({c, d} : Finset ℕ) := by simp [h23, h24]
  have hnot3 : c ∉ ({d} : Finset ℕ) := by simp [h34]
  refine ⟨?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hnot1, Finset.card_insert_of_notMem hnot2,
      Finset.card_insert_of_notMem hnot3, Finset.card_singleton]
  · rw [Finset.sum_insert hnot1, Finset.sum_insert hnot2,
      Finset.sum_insert hnot3, Finset.sum_singleton]

lemma coprime_four_of_coprime_first_two {a b c d : ℕ} (hab : Nat.Coprime a b) :
    ({a, b, c, d} : Finset ℕ).Coprime := by
  rw [Finset.Coprime, Finset.gcd_insert, Finset.gcd_insert]
  change Nat.gcd a (Nat.gcd b (Finset.gcd {c, d} id)) = 1
  rw [← Nat.gcd_assoc, (hab : Nat.gcd a b = 1), Nat.gcd_one_left]

lemma forall_mem_four {P : ℕ → Prop} {a b c d : ℕ}
    (ha : P a) (hb : P b) (hc : P c) (hd : P d) :
    ∀ s ∈ ({a, b, c, d} : Finset ℕ), P s := by
  intro s hs
  simp only [mem_insert, mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl
  exacts [ha, hb, hc, hd]

def family (k : ℕ) : Finset ℕ := {s1 k, s2 k, s3 k, s4 k}

lemma family_card_and_sum (k : ℕ) :
    (family k).card = 4 ∧ ∑ s ∈ family k, s = (XParam k + Y) ^ 6 := by
  obtain ⟨_, hs43, hs32⟩ := s_chain k
  obtain ⟨hcard, hsum⟩ := card_and_sum_four
    (s1_mod_two k) (s2_mod_two k) (s3_mod_two k) (s4_mod_two k) hs43 hs32
  exact ⟨hcard, hsum.trans (s_sum_eq k)⟩

lemma family_coprime (k : ℕ) : (family k).Coprime :=
  coprime_four_of_coprime_first_two (s12_coprime k)

lemma family_full (k : ℕ) : ∀ s ∈ family k, 0 < s ∧ (6 : ℕ).Full s := by
  obtain ⟨hs4_pos, hs43, hs32⟩ := s_chain k
  exact forall_mem_four
    ⟨s1_pos k, s1_full k⟩
    ⟨lt_trans (lt_trans hs4_pos hs43) hs32, s2_full k⟩
    ⟨lt_trans hs4_pos hs43, s3_full k⟩
    ⟨hs4_pos, s4_full k⟩

lemma family_mem (k : ℕ) : family k ∈ Erdos939Sums 6 := by
  obtain ⟨hcard, hsum⟩ := family_card_and_sum k
  refine ⟨hcard, family_coprime k, ?_, family_full k⟩
  rw [hsum]
  exact full_pow (le_refl 6)

lemma family_injective : Function.Injective family := by
  intro a b hab
  have hsum_eq : ∑ s ∈ family a, s = ∑ s ∈ family b, s := by rw [hab]
  rw [(family_card_and_sum a).2, (family_card_and_sum b).2] at hsum_eq
  have hXY_eq : XParam a + Y = XParam b + Y :=
    Nat.pow_left_injective (by decide : 6 ≠ 0) hsum_eq
  have hX_eq : XParam a = XParam b := Nat.add_right_cancel hXY_eq
  have hm_eq : mParam a = mParam b :=
    Nat.pow_left_injective (by decide : 6 ≠ 0) hX_eq
  dsimp [mParam] at hm_eq
  omega

theorem solution : statement := by
  intro h_all
  have h6_fin : (Erdos939Sums 6).Finite := h_all 6 (by decide)
  have h6_inf : (Erdos939Sums 6).Infinite :=
    Set.infinite_of_injective_forall_mem family_injective family_mem
  exact h6_inf h6_fin

end Challenge.Erdos939
