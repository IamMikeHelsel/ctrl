module

public import LeanControls.RobustPD

@[expose] public section
noncomputable section

namespace LeanControls

/-- A squared-coordinate estimate suffices for convergence of that coordinate. -/
theorem coordinate_tendsto_zero {z V : ℕ → ℝ}
    (hb : ∀ n, z n ^ 2 ≤ 2 * V n)
    (hlim : Filter.Tendsto V Filter.atTop (nhds 0)) :
    Filter.Tendsto z Filter.atTop (nhds 0) := by
  apply Metric.tendsto_atTop.2
  intro eps heps
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim (eps ^ 2 / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hsmall := hN n hn
  simp only [Real.dist_eq, sub_zero] at hsmall ⊢
  apply abs_lt_of_sq_lt_sq _ heps.le
  have hVlt := (le_abs_self (V n)).trans_lt hsmall
  linarith [hb n]

namespace SampledPD

open PD

/-- Nominal sampled trajectories converge to the origin under nonvanishing jitter. -/
theorem jitter_converges (h x v : ℕ → ℝ) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hminmax : hmin ≤ 1 / 6)
    (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ 1 / 6)
    (hx : ∀ n, x (n + 1) = position (h n) (x n) (v n))
    (hv : ∀ n, v (n + 1) = velocity (h n) (x n) (v n)) :
    Filter.Tendsto x Filter.atTop (nhds 0) ∧
      Filter.Tendsto v Filter.atTop (nhds 0) := by
  have hE : Filter.Tendsto (fun n => energy (x n) (v n)) Filter.atTop (nhds 0) := by
    apply geometric_tendsto_zero (fun n => energy_nonneg _ _)
      (q := 1 - hmin / 3) (by linarith) (by linarith)
    intro n
    rw [hx n, hv n]
    exact (energy_contract (hmin0.le.trans (hlo n)) (hhi n) _ _).trans
      (mul_le_mul_of_nonneg_right (by linarith [hlo n]) (energy_nonneg _ _))
  constructor
  · apply coordinate_tendsto_zero (V := fun n => energy (x n) (v n)) _ hE
    intro n
    nlinarith [energy_lower (x n) (v n), sq_nonneg (v n)]
  · apply coordinate_tendsto_zero (V := fun n => energy (x n) (v n)) _ hE
    intro n
    nlinarith [energy_lower (x n) (v n), sq_nonneg (x n)]

end SampledPD

namespace RobustPD

open PD SampledPD

/-- Construct the saturated, perturbed trajectory for every natural-number time. -/
def run (h ex ev : ℕ → ℝ) (U : ℝ) (initial : ℝ × ℝ) : ℕ → ℝ × ℝ
  | 0 => initial
  | n + 1 =>
    let z := run h ex ev U initial n
    let u := saturate U (SampledPD.control z.1 z.2)
    (z.1 + h n * z.2 + h n ^ 2 / 2 * u + ex n,
      z.2 + h n * u + ev n)

/-- A concrete nonempty certified operating envelope. The constants are normalized. -/
theorem demo_safe (h ex ev : ℕ → ℝ)
    (hlo : ∀ n, 1 / 20 ≤ h n) (hhi : ∀ n, h n ≤ 1 / 6)
    (he : ∀ n, ex n ^ 2 + ev n ^ 2 ≤ (1 / 1000 : ℝ) ^ 2) :
    ∀ n, let z := run h ex ev 1 (1 / 10, 0) n
      energy z.1 z.2 ≤ 1 / 10 ∧ |SampledPD.control z.1 z.2| ≤ 1 := by
  apply saturated_robust_invariant h
    (fun n => (run h ex ev 1 (1 / 10, 0) n).1)
    (fun n => (run h ex ev 1 (1 / 10, 0) n).2) ex ev
    (eps := 1 / 1000) (R := 1 / 10) (U := 1)
    (by norm_num) (by norm_num) hlo hhi he (by norm_num)
    (by norm_num [run, energy])
  · intro n
    rfl
  · intro n
    rfl

end RobustPD
end LeanControls
