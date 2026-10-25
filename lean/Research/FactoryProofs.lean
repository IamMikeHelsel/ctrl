import Mathlib

/-! Five bounded research helper contracts from the 2026-10-21 local-factory pilot.
R03 and M02 were drafted by local GPT-OSS 120B and repaired by Codex.
S05 was completed by local GPT-OSS 120B without proof edits.
C10 and V01 below are independently authored Codex proofs.
Exact scope, model attempts, failures and audits: work/factory/20261021/.
These are conditional mathematics, not approved Challenges or physical guarantees. -/

namespace Research.FactoryProofs

/-- Bridge actual differentiated velocity under a phase clock to the existing acceleration budget. Conditional derivative contracts; no hardware clock guarantee. -/
def clockAccelerationStatement : Prop :=
  ∀ (v c rate : ℝ → ℝ) (a acc V A S R t : ℝ),
    HasDerivAt v a (c t) → HasDerivAt c (rate t) t → HasDerivAt rate acc t →
    |v (c t)| ≤ V → |a| ≤ A → |rate t| ≤ S → |acc| ≤ R →
    0 ≤ V → 0 ≤ A → 0 ≤ S → 0 ≤ R →
    HasDerivAt (fun x => v (c x) * rate x)
      (a * (rate t)^2 + v (c t) * acc) t ∧
    |a * (rate t)^2 + v (c t) * acc| ≤ A * S^2 + V * R
theorem clockAcceleration : clockAccelerationStatement := by
  unfold clockAccelerationStatement
  intro v c rate a acc V A S R t hv hcv hrate hvV haA hrateS haccR hVpos hApos hSpos hRpos
  have hvc : HasDerivAt (fun x => v (c x)) (a * rate t) t := hv.comp t hcv
  have hprod : HasDerivAt (fun x => v (c x) * rate x)
      ((a * rate t) * rate t + v (c t) * acc) t := hvc.mul hrate
  have hderiv : HasDerivAt (fun x => v (c x) * rate x)
      (a * (rate t) ^ 2 + v (c t) * acc) t := by
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hprod
  have h_abs_le : |a * (rate t) ^ 2 + v (c t) * acc| ≤ A * S ^ 2 + V * R := by
    have h1 : |a * (rate t) ^ 2 + v (c t) * acc| ≤
        |a * (rate t) ^ 2| + |v (c t) * acc| := by
      exact abs_add_le (a * (rate t) ^ 2) (v (c t) * acc)
    have h2 : |a * (rate t) ^ 2| ≤ A * S ^ 2 := by
      have h_rate_sq : |rate t| ^ 2 ≤ S ^ 2 := by
        have := mul_le_mul hrateS hrateS (abs_nonneg _) hSpos
        simpa [pow_two] using this
      calc
        |a * (rate t) ^ 2| = |a| * |rate t| ^ 2 := by rw [abs_mul, abs_pow]
        _ ≤ A * S ^ 2 := mul_le_mul haA h_rate_sq (sq_nonneg _) hApos
    have h3 : |v (c t) * acc| ≤ V * R := by
      simpa [abs_mul] using mul_le_mul hvV haccR (abs_nonneg _) hVpos
    have h4 : |a * (rate t) ^ 2| + |v (c t) * acc| ≤ A * S ^ 2 + V * R :=
      add_le_add h2 h3
    exact le_trans h1 h4
  exact ⟨hderiv, h_abs_le⟩

#print axioms clockAcceleration

/-- Finite union-capacity obstruction for residue-cover certificates. Does not prove the infinite tail, admissible-modulus coverage or Erdos 273. -/
def finiteCoverBudgetStatement : Prop :=
  ∀ {α : Type} [DecidableEq α] (U : Finset α) (k : ℕ)
    (C : Fin k → Finset α) (cap : Fin k → ℕ),
    (∀ i, (U ∩ C i).card ≤ cap i) →
    (∑ i, cap i) < U.card →
    ¬ (∀ x ∈ U, ∃ i, x ∈ C i)
theorem finiteCoverBudget : finiteCoverBudgetStatement := by
  unfold finiteCoverBudgetStatement
  intro α _inst U k C cap hcap hlt hforall
  have hUsub : U ⊆ (Finset.univ.biUnion fun i => U ∩ C i) := by
    intro x hxU
    rcases hforall x hxU with ⟨i, hi⟩
    have : x ∈ U ∩ C i := by
      exact Finset.mem_inter.mpr ⟨hxU, hi⟩
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, this⟩
  have hcardUle : U.card ≤ (Finset.univ.biUnion fun i => U ∩ C i).card :=
    Finset.card_le_card hUsub
  have hcard_le_sum : (Finset.univ.biUnion fun i => U ∩ C i).card ≤ ∑ i, cap i := by
    have hle : (Finset.univ.biUnion fun i => U ∩ C i).card ≤
        ∑ i, (U ∩ C i).card := by
      simpa using Finset.card_biUnion_le (s:=Finset.univ) (t:=fun i => U ∩ C i)
    refine le_trans hle ?_
    refine Finset.sum_le_sum ?_
    intro i hi
    exact hcap i
  have : U.card ≤ ∑ i, cap i := le_trans hcardUle hcard_le_sum
  exact not_lt.mpr this hlt

#print axioms finiteCoverBudget

/-- Exact finite-horizon recurrence envelope retaining the initial transient. No contraction or physical model assumptions are inferred. -/
def transientEnvelopeStatement : Prop :=
  ∀ (x : ℕ → ℝ) (ρ ε L : ℝ), 0 ≤ ρ →
    ε ≤ (1 - ρ) * L →
    (∀ n, x (n + 1) ≤ ρ * x n + ε) →
    ∀ n, x n ≤ ρ^n * (x 0 - L) + L
theorem transientEnvelope : transientEnvelopeStatement := by
  unfold transientEnvelopeStatement
  intro x ρ ε L hρ hε hstep n
  induction n with
  | zero => simp
  | succ n ih =>
    have hm := mul_le_mul_of_nonneg_left ih hρ
    have hs := hstep n
    rw [pow_succ]
    nlinarith

#print axioms transientEnvelope

/-- All-time within-hold safety transfer from an explicit pointwise remainder envelope. ODE-to-remainder proof remains a separate obligation. -/
def withinHoldSafetyStatement : Prop :=
  ∀ (q v a δ T : ℝ) (r : ℝ → ℝ),
    (∀ t ∈ Set.Icc (0 : ℝ) T, |r t| ≤ δ / 2 * t^2) →
    (∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ q + v*t + (a-δ)/2*t^2) →
    ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ q + v*t + a/2*t^2 + r t
theorem withinHoldSafety : withinHoldSafetyStatement := by
  unfold withinHoldSafetyStatement
  intro q v a δ T r hr hq t ht
  have h_abs : |r t| ≤ δ / 2 * t ^ 2 := hr t ht
  have h_bounds := (abs_le).mp h_abs
  rcases h_bounds with ⟨h_neg, h_pos⟩
  have h_nonneg : 0 ≤ δ / 2 * t ^ 2 + r t := by
    have : - (δ / 2 * t ^ 2) ≤ r t := h_neg
    linarith
  have h_quad_nonneg : 0 ≤ q + v * t + (a - δ) / 2 * t ^ 2 := hq t ht
  have h_eq : q + v * t + a / 2 * t ^ 2 + r t =
      (q + v * t + (a - δ) / 2 * t ^ 2) + (δ / 2 * t ^ 2 + r t) := by
    ring
  have : 0 ≤ q + v * t + a / 2 * t ^ 2 + r t := by
    simpa [h_eq] using add_nonneg h_quad_nonneg h_nonneg
  exact this

#print axioms withinHoldSafety

/-- Calibrated scalar projective-chart perturbation bound with a positive-depth margin. Does not certify pose uniqueness, calibration or a full homography. -/
def positiveDepthErrorStatement : Prop :=
  ∀ (x z dx dz ε : ℝ), 0 ≤ ε → ε < z → |dz| ≤ ε →
    0 < z + dz ∧
    |(x+dx)/(z+dz) - x/z| ≤ (|dx| * z + |x| * ε) / (z * (z - ε))
theorem positiveDepthError : positiveDepthErrorStatement := by
  unfold positiveDepthErrorStatement
  intro x z dx dz ε he hz hdz
  have hzpos : 0 < z := lt_of_le_of_lt he hz
  have hlo := (abs_le.mp hdz).1
  have hzp : 0 < z + dz := by linarith
  have hmargin : 0 < z - ε := sub_pos.mpr hz
  have hd1 : 0 < z * (z + dz) := mul_pos hzpos hzp
  have hd2 : 0 < z * (z - ε) := mul_pos hzpos hmargin
  refine ⟨hzp, ?_⟩
  have hid : (x + dx) / (z + dz) - x / z =
      (dx * z - x * dz) / (z * (z + dz)) := by
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos hd1]
  apply (div_le_div_iff₀ hd1 hd2).mpr
  have hn : |dx * z - x * dz| ≤ |dx| * z + |x| * ε := by
    calc
      |dx * z - x * dz| ≤ |dx * z| + |x * dz| := by
        simpa only [sub_zero, zero_sub, abs_neg] using (abs_sub_le (dx * z) 0 (x * dz))
      _ = |dx| * z + |x| * |dz| := by rw [abs_mul, abs_mul, abs_of_pos hzpos]
      _ ≤ |dx| * z + |x| * ε :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hdz (abs_nonneg x))
  have hb : 0 ≤ |dx| * z + |x| * ε :=
    add_nonneg (mul_nonneg (abs_nonneg dx) hzpos.le) (mul_nonneg (abs_nonneg x) he)
  have hd : z * (z - ε) ≤ z * (z + dz) :=
    mul_le_mul_of_nonneg_left (by linarith) hzpos.le
  exact (mul_le_mul_of_nonneg_right hn hd2.le).trans (mul_le_mul_of_nonneg_left hd hb)

#print axioms positiveDepthError

end Research.FactoryProofs
