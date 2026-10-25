import Challenge.Erdos273

open Erdos273 Pointwise

namespace Challenge.Erdos273

set_option maxRecDepth 20000

/-- The 12 distinct moduli `p - 1` dividing 360. -/
def mods : Fin 12 → ℕ := ![2, 4, 6, 10, 12, 18, 30, 36, 40, 60, 72, 180]

/-- The corresponding residues `r_i < m_i`. -/
def res : Fin 12 → ℕ := ![1, 0, 0, 0, 2, 4, 4, 10, 2, 46, 70, 178]

/-- The corresponding primes `p_i = m_i + 1 ≥ 3`. -/
def primes : Fin 12 → ℕ := ![3, 5, 7, 11, 13, 19, 31, 37, 41, 61, 73, 181]

lemma mods_dvd_360 : ∀ i : Fin 12, mods i ∣ 360 := by decide

lemma mods_ge_two : ∀ i : Fin 12, 2 ≤ mods i := by decide

lemma mods_injective : Function.Injective mods := by decide

lemma cov_360 : ∀ r : Fin 360, ∃ i : Fin 12, r.val % mods i = res i := by decide

lemma primes_spec :
    ∀ i : Fin 12, (primes i).Prime ∧ 3 ≤ primes i ∧ mods i = primes i - 1 := by decide

lemma mem_span_singleton_iff_dvd (m x : ℕ) :
    x ∈ (Ideal.span {m} : Ideal ℕ) ↔ m ∣ x := by
  rw [Ideal.span, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, mul_comm a m⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, mul_comm a m⟩

theorem solution : statement := by
  refine ⟨{
    ι := Fin 12
    residue := res
    moduli := fun i => Ideal.span {mods i}
    unionCovers := by
      rw [Set.eq_univ_iff_forall]
      intro n
      rw [Set.mem_iUnion]
      let r : Fin 360 := ⟨n % 360, Nat.mod_lt n (by decide)⟩
      obtain ⟨i, hi⟩ := cov_360 r
      refine ⟨i, ?_⟩
      have hmod : n % mods i = res i := by
        rw [← Nat.mod_mod_of_dvd n (mods_dvd_360 i)]
        exact hi
      have hmem_res : res i ∈ ({res i} : Set ℕ) := Set.mem_singleton (res i)
      have hmem_mod : mods i * (n / mods i) ∈ (Ideal.span {mods i} : Set ℕ) := by
        change mods i * (n / mods i) ∈ (Ideal.span {mods i} : Ideal ℕ)
        rw [mem_span_singleton_iff_dvd]
        exact ⟨n / mods i, rfl⟩
      have hsum := Set.add_mem_add hmem_res hmem_mod
      have h_eq : res i + mods i * (n / mods i) = n := by
        rw [← hmod, Nat.mod_add_div]
      rwa [h_eq] at hsum
    ne_bot := by
      intro i hbot
      have hmem : mods i ∈ (Ideal.span {mods i} : Ideal ℕ) :=
        Ideal.subset_span (Set.mem_singleton (mods i))
      rw [hbot, Submodule.mem_bot] at hmem
      have hge := mods_ge_two i
      omega
    ne_top := by
      intro i htop
      have hmem : (1 : ℕ) ∈ (Ideal.span {mods i} : Ideal ℕ) := by
        rw [htop]
        trivial
      rw [mem_span_singleton_iff_dvd] at hmem
      have hle : mods i ≤ 1 := Nat.le_of_dvd (by decide) hmem
      have hge := mods_ge_two i
      omega
    injective_moduli := by
      intro i j hij
      dsimp at hij
      have h1 : mods i ∈ (Ideal.span {mods j} : Ideal ℕ) := by
        rw [← hij]
        exact Ideal.subset_span (Set.mem_singleton (mods i))
      have h2 : mods j ∈ (Ideal.span {mods i} : Ideal ℕ) := by
        rw [hij]
        exact Ideal.subset_span (Set.mem_singleton (mods j))
      rw [mem_span_singleton_iff_dvd] at h1 h2
      exact mods_injective (Nat.dvd_antisymm h2 h1)
  }, ?_⟩
  intro i
  obtain ⟨hp, hge, hmod⟩ := primes_spec i
  exact ⟨primes i, hp, hge, by simp [hmod]⟩

end Challenge.Erdos273
