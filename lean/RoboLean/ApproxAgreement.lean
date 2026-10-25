import Mathlib

/-!
# Byzantine approximate agreement: one round halves the spread

With `n = |G| + f > 3f` (correct values `G` in `[lo, hi]`, `f` faulty values per receiver),
the trimmed-midpoint update (drop the `f` smallest and `f` largest, take the midpoint of the
rest) is valid (`mid_mem`) and halves the spread between correct receivers (`mid_close`).
`spread_after_rounds` iterates this: after `k` rounds the spread is `≤ (hi - lo) / 2 ^ k`.
-/

namespace ApproxAgreement

/-- Sort the received values and drop the `f` smallest and `f` largest. -/
noncomputable def trim (f : ℕ) (L : Multiset ℝ) : List ℝ :=
  ((L.sort (· ≤ ·)).drop f).take (L.card - 2 * f)

/-- Midpoint of the trimmed values (the Dolev–Lynch–Pinter–Stark–Weihl update rule). -/
noncomputable def mid (f : ℕ) (L : Multiset ℝ) : ℝ :=
  ((trim f L).head?.getD 0 + (trim f L).getLast?.getD 0) / 2

/-! ### Helper lemmas: order-statistic counting -/

lemma countP_mono_imp {p q : ℝ → Prop} [DecidablePred p] [DecidablePred q]
    (h : ∀ x, p x → q x) (G : Multiset ℝ) : G.countP p ≤ G.countP q := by
  induction G using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.countP_cons]
    by_cases hp : p a
    · simp [hp, h a hp]; omega
    · simp only [hp, if_false]; split_ifs <;> omega

/-- In a sorted list, at least `i + 1` entries are `≤ l[i]`. -/
lemma list_countP_le_get (l : List ℝ) (hl : l.Pairwise (· ≤ ·)) (i : ℕ) (hi : i < l.length) :
    i + 1 ≤ l.countP (fun x => decide (x ≤ l[i])) := by
  rw [show l.countP (fun x => decide (x ≤ l[i])) = _ from
    (congrArg (List.countP (fun x => decide (x ≤ l[i]))) (List.take_append_drop (i + 1) l)).symm,
    List.countP_append]
  have : (l.take (i + 1)).countP (fun x => decide (x ≤ l[i])) = (l.take (i + 1)).length := by
    rw [List.countP_eq_length]
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    simp only [List.length_take] at hj
    simp only [List.getElem_take, decide_eq_true_eq]
    rcases Nat.lt_or_ge j i with h | h
    · exact List.pairwise_iff_getElem.1 hl j i (by omega) hi h
    · have : j = i := by omega
      subst this; exact le_rfl
  rw [this, List.length_take]; omega

/-- In a sorted list, at least `length - i` entries are `≥ l[i]`. -/
lemma list_countP_ge_get (l : List ℝ) (hl : l.Pairwise (· ≤ ·)) (i : ℕ) (hi : i < l.length) :
    l.length - i ≤ l.countP (fun x => decide (l[i] ≤ x)) := by
  rw [show l.countP (fun x => decide (l[i] ≤ x)) = _ from
    (congrArg (List.countP (fun x => decide (l[i] ≤ x))) (List.take_append_drop i l)).symm,
    List.countP_append]
  have : (l.drop i).countP (fun x => decide (l[i] ≤ x)) = (l.drop i).length := by
    rw [List.countP_eq_length]
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    simp only [List.length_drop] at hj
    simp only [List.getElem_drop, decide_eq_true_eq]
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; simp
    · exact List.pairwise_iff_getElem.1 hl i (i + j) hi (by omega) (by omega)
  rw [this, List.length_drop]; omega

lemma sort_length (L : Multiset ℝ) : (L.sort (· ≤ ·)).length = L.card :=
  Multiset.length_sort _

lemma countP_le_sort (L : Multiset ℝ) (i : ℕ) (hi : i < (L.sort (· ≤ ·)).length) :
    i + 1 ≤ L.countP (· ≤ (L.sort (· ≤ ·))[i]) := by
  rw [show L.countP (· ≤ (L.sort (· ≤ ·))[i]) = _ from
    congrArg (Multiset.countP (· ≤ (L.sort (· ≤ ·))[i])) (Multiset.sort_eq L (· ≤ ·)).symm,
    Multiset.coe_countP]
  exact list_countP_le_get _ (Multiset.pairwise_sort _ _) i hi

lemma countP_ge_sort (L : Multiset ℝ) (i : ℕ) (hi : i < (L.sort (· ≤ ·)).length) :
    L.card - i ≤ L.countP ((L.sort (· ≤ ·))[i] ≤ ·) := by
  rw [show L.countP ((L.sort (· ≤ ·))[i] ≤ ·) = _ from
    congrArg (Multiset.countP ((L.sort (· ≤ ·))[i] ≤ ·)) (Multiset.sort_eq L (· ≤ ·)).symm,
    Multiset.coe_countP, ← sort_length L]
  exact list_countP_ge_get _ (Multiset.pairwise_sort _ _) i hi

/-- Counting through the faulty values: `countP p G ≥ countP p (G + B) - f`. -/
lemma countP_good (p : ℝ → Prop) [DecidablePred p] (G B : Multiset ℝ) (f : ℕ) (hB : B.card = f) :
    (G + B).countP p ≤ G.countP p + f := by
  rw [Multiset.countP_add, ← hB]
  have := Multiset.countP_le_card p B
  omega

lemma lo_le_of_count (G B : Multiset ℝ) (f : ℕ) (lo hi v : ℝ) (hG : ∀ x ∈ G, lo ≤ x ∧ x ≤ hi)
    (hB : B.card = f) (h : f < (G + B).countP (· ≤ v)) : lo ≤ v := by
  have h1 := countP_good (· ≤ v) G B f hB
  obtain ⟨x, hx, hxv⟩ := Multiset.countP_pos.1 (show 0 < G.countP (· ≤ v) by omega)
  exact (hG x hx).1.trans hxv

lemma le_hi_of_count (G B : Multiset ℝ) (f : ℕ) (lo hi v : ℝ) (hG : ∀ x ∈ G, lo ≤ x ∧ x ≤ hi)
    (hB : B.card = f) (h : f < (G + B).countP (v ≤ ·)) : v ≤ hi := by
  have h1 := countP_good (v ≤ ·) G B f hB
  obtain ⟨x, hx, hxv⟩ := Multiset.countP_pos.1 (show 0 < G.countP (v ≤ ·) by omega)
  exact hxv.trans (hG x hx).2

/-- The first and last trimmed values are the order statistics at `f` and `n - f - 1`. -/
lemma mid_eq (f : ℕ) (L : Multiset ℝ) (hn : 2 * f < L.card) :
    mid f L = ((L.sort (· ≤ ·))[f]'(by rw [sort_length]; omega) +
      (L.sort (· ≤ ·))[L.card - f - 1]'(by rw [sort_length]; omega)) / 2 := by
  have hlen : (trim f L).length = L.card - 2 * f := by
    simp only [trim, List.length_take, List.length_drop, sort_length]; omega
  unfold mid
  rw [List.head?_eq_getElem?, List.getLast?_eq_getElem?, hlen]
  congr 2
  · simp only [trim, List.getElem?_take, List.getElem?_drop]
    rw [if_pos (by omega), List.getElem?_eq_getElem (by rw [sort_length]; omega)]
    simp
  · simp only [trim, List.getElem?_take, List.getElem?_drop]
    rw [if_pos (by omega), List.getElem?_eq_getElem (by rw [sort_length]; omega)]
    simp only [Option.getD_some]
    congr 1; omega

/-- Every kept order statistic lies in `[lo, hi]`. -/
lemma stat_mem (f : ℕ) (G B : Multiset ℝ) (lo hi : ℝ)
    (hG : ∀ x ∈ G, lo ≤ x ∧ x ≤ hi) (hB : B.card = f) (i : ℕ)
    (hi1 : f ≤ i) (hi2 : i + f < (G + B).card) :
    lo ≤ ((G + B).sort (· ≤ ·))[i]'(by rw [sort_length]; omega) ∧
      ((G + B).sort (· ≤ ·))[i]'(by rw [sort_length]; omega) ≤ hi := by
  have hl : i < ((G + B).sort (· ≤ ·)).length := by rw [sort_length]; omega
  constructor
  · apply lo_le_of_count G B f lo hi _ hG hB
    have := countP_le_sort (G + B) i hl; omega
  · apply le_hi_of_count G B f lo hi _ hG hB
    have := countP_ge_sort (G + B) i hl; omega

/-- Key crossing lemma: the low kept value of one receiver is at most the high kept value of
another. -/
lemma low_le_high (f : ℕ) (G B₁ B₂ : Multiset ℝ)
    (hB₁ : B₁.card = f) (hB₂ : B₂.card = f) (hn : 2 * f < G.card) :
    ((G + B₁).sort (· ≤ ·))[f]'(by rw [sort_length, Multiset.card_add]; omega) ≤
      ((G + B₂).sort (· ≤ ·))[(G + B₂).card - f - 1]'(by
        rw [sort_length, Multiset.card_add]; omega) := by
  have c1 := countP_ge_sort (G + B₁) f (by rw [sort_length, Multiset.card_add]; omega)
  have c2 := countP_le_sort (G + B₂) ((G + B₂).card - f - 1)
    (by rw [sort_length, Multiset.card_add]; omega)
  set a := ((G + B₁).sort (· ≤ ·))[f]'(by rw [sort_length, Multiset.card_add]; omega)
  set A := ((G + B₂).sort (· ≤ ·))[(G + B₂).card - f - 1]'(by
        rw [sort_length, Multiset.card_add]; omega)
  have g1 := countP_good (a ≤ ·) G B₁ f hB₁
  have g2 := countP_good (· ≤ A) G B₂ f hB₂
  have e1 : (G + B₁).card = G.card + f := by rw [Multiset.card_add, hB₁]
  have e2 : (G + B₂).card = G.card + f := by rw [Multiset.card_add, hB₂]
  by_contra hlt
  push Not at hlt
  have hm := countP_mono_imp (p := (a ≤ ·)) (q := fun x => ¬ x ≤ A)
    (fun x hx hxA => absurd (lt_of_lt_of_le hlt hx) (not_lt.2 hxA)) G
  have hc := Multiset.card_eq_countP_add_countP (· ≤ A) G
  omega

theorem mid_close (f : ℕ) (G B₁ B₂ : Multiset ℝ) (lo hi : ℝ)
    (hG : ∀ x ∈ G, lo ≤ x ∧ x ≤ hi) (hB₁ : B₁.card = f) (hB₂ : B₂.card = f)
    (hn : 2 * f < G.card) :
    |mid f (G + B₁) - mid f (G + B₂)| ≤ (hi - lo) / 2 := by
  have e1 : (G + B₁).card = G.card + f := by rw [Multiset.card_add, hB₁]
  have e2 : (G + B₂).card = G.card + f := by rw [Multiset.card_add, hB₂]
  rw [mid_eq f _ (by omega), mid_eq f _ (by omega)]
  have m1 := stat_mem f G B₁ lo hi hG hB₁ f le_rfl (by omega)
  have m2 := stat_mem f G B₂ lo hi hG hB₂ f le_rfl (by omega)
  have M1 := stat_mem f G B₁ lo hi hG hB₁ ((G + B₁).card - f - 1) (by omega) (by omega)
  have M2 := stat_mem f G B₂ lo hi hG hB₂ ((G + B₂).card - f - 1) (by omega) (by omega)
  have x12 := low_le_high f G B₁ B₂ hB₁ hB₂ hn
  have x21 := low_le_high f G B₂ B₁ hB₂ hB₁ hn
  rw [abs_le]
  constructor <;> linarith

/-- The update stays inside the correct range (validity). -/
theorem mid_mem (f : ℕ) (G B : Multiset ℝ) (lo hi : ℝ)
    (hG : ∀ x ∈ G, lo ≤ x ∧ x ≤ hi) (hB : B.card = f) (hn : 2 * f < G.card) :
    lo ≤ mid f (G + B) ∧ mid f (G + B) ≤ hi := by
  have e : (G + B).card = G.card + f := by rw [Multiset.card_add, hB]
  rw [mid_eq f _ (by omega)]
  have m := stat_mem f G B lo hi hG hB f le_rfl (by omega)
  have M := stat_mem f G B lo hi hG hB ((G + B).card - f - 1) (by omega) (by omega)
  constructor <;> linarith

/-! ### Iterating the round -/

/-- Abstract iteration: a quantity that at least halves every round is `≤ D 0 / 2 ^ k`
after `k` rounds. -/
theorem halving_iter (D : ℕ → ℝ) (h : ∀ k, D (k + 1) ≤ D k / 2) (k : ℕ) :
    D k ≤ D 0 / 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc D (k + 1) ≤ D k / 2 := h k
      _ ≤ D 0 / 2 ^ k / 2 := by linarith
      _ = D 0 / 2 ^ (k + 1) := by rw [pow_succ, div_div]

/-- **`k` rounds of approximate agreement.** The correct nodes are a finite type `ι` with
`|ι| > 2f`. In round `k` correct node `i` holds `x k i`; it receives all correct values
(the multiset `G k`) plus `f` arbitrary faulty values `B k i`, and updates to the trimmed
midpoint. If initially all correct values lie in `[lo, hi]`, then after `k` rounds any two
correct values differ by at most `(hi - lo) / 2 ^ k`. -/
theorem spread_after_rounds {ι : Type*} [Fintype ι] (f : ℕ) (hn : 2 * f < Fintype.card ι)
    (x : ℕ → ι → ℝ) (B : ℕ → ι → Multiset ℝ) (hB : ∀ k i, (B k i).card = f)
    (hstep : ∀ k i, x (k + 1) i = mid f ((Finset.univ.val.map (x k)) + B k i))
    (lo hi : ℝ) (h0 : ∀ i, lo ≤ x 0 i ∧ x 0 i ≤ hi) (k : ℕ) :
    ∀ i j, |x k i - x k j| ≤ (hi - lo) / 2 ^ k := by
  have hne : (Finset.univ : Finset ι).Nonempty := by
    rw [Finset.univ_nonempty_iff, ← Fintype.card_pos_iff]; omega
  induction k with
  | zero =>
    intro i j
    simp only [pow_zero, div_one, abs_le]
    constructor <;> linarith [h0 i, h0 j]
  | succ k ih =>
    intro i j
    obtain ⟨a, -, ha⟩ := Finset.exists_min_image Finset.univ (x k) hne
    obtain ⟨b, -, hb⟩ := Finset.exists_max_image Finset.univ (x k) hne
    have hG : ∀ y ∈ Finset.univ.val.map (x k), x k a ≤ y ∧ y ≤ x k b := by
      intro y hy
      obtain ⟨c, -, rfl⟩ := Multiset.mem_map.1 hy
      exact ⟨ha c (Finset.mem_univ _), hb c (Finset.mem_univ _)⟩
    have hc := mid_close f _ (B k i) (B k j) (x k a) (x k b) hG (hB k i) (hB k j)
      (by simpa using hn)
    rw [← hstep, ← hstep] at hc
    have hab := (abs_le.1 (ih b a)).2
    calc |x (k + 1) i - x (k + 1) j| ≤ (x k b - x k a) / 2 := hc
      _ ≤ (hi - lo) / 2 ^ k / 2 := by linarith
      _ = (hi - lo) / 2 ^ (k + 1) := by rw [pow_succ, div_div]

end ApproxAgreement
