import Erdos128.ExternalInputs
import Erdos128.GraphRational

set_option linter.style.header false

/-!
# Finite cut parameters for the low-density branch

This module turns the unoriented BCL witness into a small side `X`, a nonempty
large side `Y`, and the exact rational parameters used by the paper.
-/

namespace Erdos128

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A BCL cut oriented so that `small` has no more vertices than its
complement. -/
structure OrientedBCLCut
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  small : Finset V
  card_le_compl : small.card ≤ smallᶜ.card
  internal_bound :
    ((edgeCountOn G small + edgeCountOn G smallᶜ : ℕ) : ℚ) ≤
      (2 / 47 : ℚ) * (Fintype.card V : ℚ) ^ 2

/-- Orient an arbitrary BCL witness by complementing it when necessary. -/
theorem exists_orientedBCLCut
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : BCLCutCertificate G) :
    Nonempty (OrientedBCLCut G) := by
  classical
  obtain ⟨S, hS⟩ := h
  by_cases hcard : S.card ≤ Sᶜ.card
  · exact ⟨⟨S, hcard, hS⟩⟩
  · refine ⟨⟨Sᶜ, ?_, ?_⟩⟩
    · simpa using Nat.le_of_lt (lt_of_not_ge hcard)
    · simpa [add_comm] using hS

namespace OrientedBCLCut

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The large side of an oriented cut. -/
def large (C : OrientedBCLCut G) : Finset V := C.smallᶜ

theorem small_card_add_large_card (C : OrientedBCLCut G) :
    C.small.card + C.large.card = Fintype.card V := by
  have hle : C.small.card ≤ Fintype.card V := Finset.card_le_univ _
  simp only [large, Finset.card_compl]
  omega

theorem large_nonempty [Nonempty V] (C : OrientedBCLCut G) :
    C.large.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hzero
  have hcard0 : C.large.card = 0 := by simp [hzero]
  have hle : C.small.card ≤ C.large.card := by
    simpa [large] using C.card_le_compl
  have hsmall0 : C.small.card = 0 := by omega
  have hn0 : Fintype.card V = 0 := by
    have := C.small_card_add_large_card
    omega
  exact (Fintype.card_ne_zero (α := V)) hn0

theorem card_le_two_mul_large (C : OrientedBCLCut G) :
    Fintype.card V ≤ 2 * C.large.card := by
  have hsum := C.small_card_add_large_card
  have hle := C.card_le_compl
  change C.small.card ≤ C.large.card at hle
  omega

theorem large_card_le_card (C : OrientedBCLCut G) :
    C.large.card ≤ Fintype.card V := by
  have hsum := C.small_card_add_large_card
  omega

/-- The paper's parameter `c = n / (2 |Y|)`. -/
def c (C : OrientedBCLCut G) : ℚ :=
  (Fintype.card V : ℚ) / (2 * (C.large.card : ℚ))

/-- The imbalance parameter `a = 1 - c`. -/
def a (C : OrientedBCLCut G) : ℚ := 1 - C.c

/-- The normalized internal edge mass of the uniformly weighted large side. -/
def mu (C : OrientedBCLCut G) : ℚ :=
  (edgeCountOn G C.large : ℚ) / (C.large.card : ℚ) ^ 2

/-- Rational form of the cap used by the existing real calculus module. -/
def capQ (a : ℚ) : ℚ :=
  4 * (2 / 47 : ℚ) * (1 - a) ^ 2

theorem c_pos [Nonempty V] (C : OrientedBCLCut G) : 0 < C.c := by
  unfold c
  have hk : (0 : ℚ) < (C.large.card : ℚ) := by
    exact_mod_cast C.large_nonempty.card_pos
  positivity

theorem c_le_one [Nonempty V] (C : OrientedBCLCut G) : C.c ≤ 1 := by
  unfold c
  have hk : (0 : ℚ) < 2 * (C.large.card : ℚ) := by
    have : (0 : ℚ) < (C.large.card : ℚ) := by
      exact_mod_cast C.large_nonempty.card_pos
    positivity
  rw [div_le_one hk]
  exact_mod_cast C.card_le_two_mul_large

theorem one_half_le_c [Nonempty V] (C : OrientedBCLCut G) :
    (1 / 2 : ℚ) ≤ C.c := by
  unfold c
  have hk : (0 : ℚ) < 2 * (C.large.card : ℚ) := by
    have : (0 : ℚ) < (C.large.card : ℚ) := by
      exact_mod_cast C.large_nonempty.card_pos
    positivity
  rw [le_div_iff₀ hk]
  have hkn : (C.large.card : ℚ) ≤ Fintype.card V := by
    exact_mod_cast C.large_card_le_card
  linarith

theorem a_mem_Icc [Nonempty V] (C : OrientedBCLCut G) :
    0 ≤ C.a ∧ C.a ≤ 1 / 2 := by
  constructor
  · unfold a
    linarith [C.c_le_one]
  · unfold a
    linarith [C.one_half_le_c]

theorem mu_nonneg (C : OrientedBCLCut G) : 0 ≤ C.mu := by
  unfold mu
  positivity

theorem mu_le_capQ [Nonempty V] (C : OrientedBCLCut G) :
    C.mu ≤ capQ C.a := by
  have hkNat := C.large_nonempty.card_pos
  have hk : (0 : ℚ) < (C.large.card : ℚ) := by exact_mod_cast hkNat
  have heY : (edgeCountOn G C.large : ℚ) ≤
      (2 / 47 : ℚ) * (Fintype.card V : ℚ) ^ 2 := by
    have hnonneg : (0 : ℚ) ≤ edgeCountOn G C.small := by positivity
    have hbound := C.internal_bound
    change ((edgeCountOn G C.small + edgeCountOn G C.large : ℕ) : ℚ) ≤ _ at hbound
    push_cast at hbound
    linarith
  unfold mu capQ a c
  rw [div_le_iff₀ (sq_pos_of_pos hk)]
  field_simp
  nlinarith [sq_nonneg (Fintype.card V : ℚ)]

end OrientedBCLCut

end

end Erdos128
