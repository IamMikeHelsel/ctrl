module

public import LeanControls.Quantized

@[expose] public section

noncomputable section

namespace LeanControls.SaturatedEntry

open PD SampledPD RobustPD

/-- Exact held step, with rounded state feedback and a unit actuator limit. -/

def step (h w : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=

  let u := Quantized.input (1 / 10000) 1 z.1 z.2 + w

  (z.1 + h * z.2 + h ^ 2 / 2 * u, z.2 + h * u)

/-- The actual trajectory is defined for every sample index. -/

def run (h w : ℕ → ℝ) : ℕ → ℝ × ℝ

  | 0 => (1, 0)

  | n + 1 => step (h n) (w n) (run h w n)

/-- Untrusted rational witness data, checked below against the actual rounded update. -/

def prefixState : ℕ → ℝ × ℝ

  | 0 => (1, 0)

  | 1 => ((199 / 200), (-1 / 10))

  | 2 => ((49 / 50), (-1 / 5))

  | 3 => ((191 / 200), (-3 / 10))

  | 4 => ((23 / 25), (-2 / 5))

  | 5 => ((548 / 625), (-58 / 125))

  | 6 => ((51787 / 62500), (-1563 / 3125))

  | 7 => ((777793 / 1000000), (-25791 / 50000))

  | 8 => ((72617 / 100000), (-3229 / 6250))

  | 9 => ((674993 / 1000000), (-5069 / 10000))

  | 10 => ((1250313 / 2000000), (-48983 / 100000))

  | 11 => ((1154537 / 2000000), (-46793 / 100000))

  | 12 => ((531721 / 1000000), (-22151 / 50000))

  | 13 => ((488747 / 1000000), (-20823 / 50000))

  | 14 => ((896923 / 2000000), (-1557 / 4000))

  | 15 => ((821779 / 2000000), (-36219 / 100000))

  | 16 => ((751989 / 2000000), (-33571 / 100000))

  | 17 => ((343699 / 1000000), (-1551 / 5000))

  | 18 => ((62779 / 200000), (-7147 / 25000))

  | 19 => ((572913 / 2000000), (-26289 / 100000))

  | 20 => ((130623 / 500000), (-6033 / 25000))

  | 21 => ((476243 / 2000000), (-22117 / 100000))

  | 22 => ((433883 / 2000000), (-20243 / 100000))

  | 23 => ((395131 / 2000000), (-18509 / 100000))

  | 24 => ((179857 / 1000000), (-4227 / 25000))

  | 25 => ((327373 / 2000000), (-15433 / 100000))

  | 26 => ((148931 / 1000000), (-7039 / 50000))

  | _ => (0, 0)

private theorem prefix_step_0 : prefixState 1 = step (1 / 10) 0 (prefixState 0) := by

  have hx : round ((1 : ℝ) / (1 / 10000)) = 10000 := by norm_num [round_eq_iff]

  have hv : round ((0 : ℝ) / (1 / 10000)) = 0 := by norm_num [round_eq_iff]

  norm_num [prefixState, step, Quantized.input, Quantized.quantize, hx, hv, SampledPD.control, RobustPD.saturate]

private theorem prefix_step_1 : prefixState 2 = step (1 / 10) 0 (prefixState 1) := by

  have hx : round (((199 / 200) : ℝ) / (1 / 10000)) = 9950 := by norm_num [round_eq_iff]

  have hv : round (((-1 / 10) : ℝ) / (1 / 10000)) = -1000 := by norm_num [round_eq_iff]

  norm_num [prefixState, step, Quantized.input, Quantized.quantize, hx, hv, SampledPD.control, RobustPD.saturate]

private theorem prefix_step_2 : prefixState 3 = step (1 / 10) 0 (prefixState 2) := by

  have hx : round (((49 / 50) : ℝ) / (1 / 10000)) = 9800 := by norm_num [round_eq_iff]

  have hv : round (((-1 / 5) : ℝ) / (1 / 10000)) = -2000 := by norm_num [round_eq_iff]

  norm_num [prefixState, step, Quantized.input, Quantized.quantize, hx, hv, SampledPD.control, RobustPD.saturate]

private theorem prefix_step_3 : prefixState 4 = step (1 / 10) 0 (prefixState 3) := by

  have hx : round (((191 / 200) : ℝ) / (1 / 10000)) = 9550 := by norm_num [round_eq_iff]

  have hv : round (((-3 / 10) : ℝ) / (1 / 10000)) = -3000 := by norm_num [round_eq_iff]

  norm_num [prefixState, step, Quantized.input, Quantized.quantize, hx, hv, SampledPD.control, RobustPD.saturate]

private theorem prefix_step_4 : prefixState 5 = step (1 / 10) 0 (prefixState 4) := by

  have hx : round (((23 / 25) : ℝ) / (1 / 10000)) = 9200 := by norm_num [round_eq_iff]

  have hv : round (((-2 / 5) : ℝ) / (1 / 10000)) = -4000 := by norm_num [round_eq_iff]

  norm_num [prefixState, step, Quantized.input, Quantized.quantize, hx, hv, SampledPD.control, RobustPD.saturate]

private theorem prefix_step_5 : prefixState 6 = step (1 / 10) 0 (prefixState 5) := by

  have hx : round (((548 / 625) : ℝ) / (1 / 10000)) = 8768 := by norm_num [round_eq_iff]

  have hv : round (((-58 / 125) : ℝ) / (1 / 10000)) = -4640 := by norm_num [round_eq_iff]

  norm_num [prefixState, step, Quantized.input, Quantized.quantize, hx, hv, SampledPD.control, RobustPD.saturate]

private theorem prefix_step_6 : prefixState 7 = step (1 / 10) 0 (prefixState 6) := by

  have hx : round (((51787 / 62500) : ℝ) / (1 / 10000)) = 8286 := by norm_num [round_eq_iff]

  have hv : round (((-1563 / 3125) : ℝ) / (1 / 10000)) = -5002 := by norm_num [round_eq_iff]

  norm_num [prefixState, step, Quantized.input, Quantized.quantize, hx, hv, SampledPD.control, RobustPD.saturate]

private theorem prefix_step_7 : prefixState 8 = step (1 / 10) 0 (prefixState 7) := by

  have hx : round (((777793 / 1000000) : ℝ) / (1 / 10000)) = 7778 := by norm_num [round_eq_iff]

  have hv : round (((-25791 / 50000) : ℝ) / (1 / 10000)) = -5158 := by norm_num [round_eq_iff]

  norm_num [prefixState, step, Quantized.input, Quantized.quantize, hx, hv, SampledPD.control, RobustPD.saturate]

private theorem prefix_step_8 : prefixState 9 = step (1 / 10) 0 (prefixState 8) := by

  have hx : round (((72617 / 100000) : ℝ) / (1 / 10000)) = 7262 := by norm_num [round_eq_iff]

  have hv : round (((-3229 / 6250) : ℝ) / (1 / 10000)) = -5166 := by norm_num [round_eq_iff]

  norm_num [prefixState, step, Quantized.input, Quantized.quantize, hx, hv, SampledPD.control, RobustPD.saturate]

private theorem prefix_step_9 : prefixState 10 = step (1 / 10) 0 (prefixState 9) := by

  have hx : round (((674993 / 1000000) : ℝ) / (1 / 10000)) = 6750 := by norm_num [round_eq_iff]

  have hv : round (((-5069 / 10000) : ℝ) / (1 / 10000)) = -5069 := by norm_num [round_eq_iff]

  norm_num [prefixState, step, Quantized.input, Quantized.quantize, hx, hv, SampledPD.control, RobustPD.saturate]

private theorem prefix_step_10 : prefixState 11 = step (1 / 10) 0 (prefixState 10) := by

  have hx : round (((1250313 / 2000000) : ℝ) / (1 / 10000)) = 6252 := by norm_num [round_eq_iff]

  have hv : round (((-48983 / 100000) : ℝ) / (1 / 10000)) = -4898 := by norm_num [round_eq_iff]

  norm_num [prefixState, step, Quantized.input, Quantized.quantize, hx, hv, SampledPD.control, RobustPD.saturate]

private theorem prefix_step_11 : prefixState 12 = step (1 / 10) 0 (prefixState 11) := by

  have hx : round (((1154537 / 2000000) : ℝ) / (1 / 10000)) = 5773 := by norm_num [round_eq_iff]

  have hv : round (((-46793 / 100000) : ℝ) / (1 / 10000)) = -4679 := by norm_num [round_eq_iff]

  norm_num [prefixState, step, Quantized.input, Quantized.quantize, hx, hv, SampledPD.control, RobustPD.saturate]

private theorem prefix_step_12 : prefixState 13 = step (1 / 10) 0 (prefixState 12) := by

  have hx : round (((531721 / 1000000) : ℝ) / (1 / 10000)) = 5317 := by norm_num [round_eq_iff]

  have hv : round (((-22151 / 50000) : ℝ) / (1 / 10000)) = -4430 := by norm_num [round_eq_iff]

  norm_num [prefixState, step, Quantized.input, Quantized.quantize, hx, hv, SampledPD.control, RobustPD.saturate]

private theorem prefix_step_13 : prefixState 14 = step (1 / 10) 0 (prefixState 13) := by

  have hx : round (((488747 / 1000000) : ℝ) / (1 / 10000)) = 4887 := by norm_num [round_eq_iff]

  have hv : round (((-20823 / 50000) : ℝ) / (1 / 10000)) = -4165 := by norm_num [round_eq_iff]

  norm_num [prefixState, step, Quantized.input, Quantized.quantize, hx, hv, SampledPD.control, RobustPD.saturate]

private theorem prefix_step_14 : prefixState 15 = step (1 / 10) 0 (prefixState 14) := by

  have hx : round (((896923 / 2000000) : ℝ) / (1 / 10000)) = 4485 := by norm_num [round_eq_iff]

  have hv : round (((-1557 / 4000) : ℝ) / (1 / 10000)) = -3892 := by norm_num [round_eq_iff]

  norm_num [prefixState, step, Quantized.input, Quantized.quantize, hx, hv, SampledPD.control, RobustPD.saturate]

private theorem prefix_step_15 : prefixState 16 = step (1 / 10) 0 (prefixState 15) := by

  have hx : round (((821779 / 2000000) : ℝ) / (1 / 10000)) = 4109 := by norm_num [round_eq_iff]

  have hv : round (((-36219 / 100000) : ℝ) / (1 / 10000)) = -3622 := by norm_num [round_eq_iff]

  norm_num [prefixState, step, Quantized.input, Quantized.quantize, hx, hv, SampledPD.control, RobustPD.saturate]

private theorem prefix_step_16 : prefixState 17 = step (1 / 10) 0 (prefixState 16) := by

  have hx : round (((751989 / 2000000) : ℝ) / (1 / 10000)) = 3760 := by norm_num [round_eq_iff]

  have hv : round (((-33571 / 100000) : ℝ) / (1 / 10000)) = -3357 := by norm_num [round_eq_iff]

  norm_num [prefixState, step, Quantized.input, Quantized.quantize, hx, hv, SampledPD.control, RobustPD.saturate]

private theorem prefix_step_17 : prefixState 18 = step (1 / 10) 0 (prefixState 17) := by

  have hx : round (((343699 / 1000000) : ℝ) / (1 / 10000)) = 3437 := by norm_num [round_eq_iff]

  have hv : round (((-1551 / 5000) : ℝ) / (1 / 10000)) = -3102 := by norm_num [round_eq_iff]

  norm_num [prefixState, step, Quantized.input, Quantized.quantize, hx, hv, SampledPD.control, RobustPD.saturate]

private theorem prefix_step_18 : prefixState 19 = step (1 / 10) 0 (prefixState 18) := by

  have hx : round (((62779 / 200000) : ℝ) / (1 / 10000)) = 3139 := by norm_num [round_eq_iff]

  have hv : round (((-7147 / 25000) : ℝ) / (1 / 10000)) = -2859 := by norm_num [round_eq_iff]

  norm_num [prefixState, step, Quantized.input, Quantized.quantize, hx, hv, SampledPD.control, RobustPD.saturate]

private theorem prefix_step_19 : prefixState 20 = step (1 / 10) 0 (prefixState 19) := by

  have hx : round (((572913 / 2000000) : ℝ) / (1 / 10000)) = 2865 := by norm_num [round_eq_iff]

  have hv : round (((-26289 / 100000) : ℝ) / (1 / 10000)) = -2629 := by norm_num [round_eq_iff]

  norm_num [prefixState, step, Quantized.input, Quantized.quantize, hx, hv, SampledPD.control, RobustPD.saturate]

private theorem prefix_step_20 : prefixState 21 = step (1 / 10) 0 (prefixState 20) := by

  have hx : round (((130623 / 500000) : ℝ) / (1 / 10000)) = 2612 := by norm_num [round_eq_iff]

  have hv : round (((-6033 / 25000) : ℝ) / (1 / 10000)) = -2413 := by norm_num [round_eq_iff]

  norm_num [prefixState, step, Quantized.input, Quantized.quantize, hx, hv, SampledPD.control, RobustPD.saturate]

private theorem prefix_step_21 : prefixState 22 = step (1 / 10) 0 (prefixState 21) := by

  have hx : round (((476243 / 2000000) : ℝ) / (1 / 10000)) = 2381 := by norm_num [round_eq_iff]

  have hv : round (((-22117 / 100000) : ℝ) / (1 / 10000)) = -2212 := by norm_num [round_eq_iff]

  norm_num [prefixState, step, Quantized.input, Quantized.quantize, hx, hv, SampledPD.control, RobustPD.saturate]

private theorem prefix_step_22 : prefixState 23 = step (1 / 10) 0 (prefixState 22) := by

  have hx : round (((433883 / 2000000) : ℝ) / (1 / 10000)) = 2169 := by norm_num [round_eq_iff]

  have hv : round (((-20243 / 100000) : ℝ) / (1 / 10000)) = -2024 := by norm_num [round_eq_iff]

  norm_num [prefixState, step, Quantized.input, Quantized.quantize, hx, hv, SampledPD.control, RobustPD.saturate]

private theorem prefix_step_23 : prefixState 24 = step (1 / 10) 0 (prefixState 23) := by

  have hx : round (((395131 / 2000000) : ℝ) / (1 / 10000)) = 1976 := by norm_num [round_eq_iff]

  have hv : round (((-18509 / 100000) : ℝ) / (1 / 10000)) = -1851 := by norm_num [round_eq_iff]

  norm_num [prefixState, step, Quantized.input, Quantized.quantize, hx, hv, SampledPD.control, RobustPD.saturate]

private theorem prefix_step_24 : prefixState 25 = step (1 / 10) 0 (prefixState 24) := by

  have hx : round (((179857 / 1000000) : ℝ) / (1 / 10000)) = 1799 := by norm_num [round_eq_iff]

  have hv : round (((-4227 / 25000) : ℝ) / (1 / 10000)) = -1691 := by norm_num [round_eq_iff]

  norm_num [prefixState, step, Quantized.input, Quantized.quantize, hx, hv, SampledPD.control, RobustPD.saturate]

private theorem prefix_step_25 : prefixState 26 = step (1 / 10) 0 (prefixState 25) := by

  have hx : round (((327373 / 2000000) : ℝ) / (1 / 10000)) = 1637 := by norm_num [round_eq_iff]

  have hv : round (((-15433 / 100000) : ℝ) / (1 / 10000)) = -1543 := by norm_num [round_eq_iff]

  norm_num [prefixState, step, Quantized.input, Quantized.quantize, hx, hv, SampledPD.control, RobustPD.saturate]

theorem prefix_step (n : ℕ) (hn : n < 26) : prefixState (n + 1) = step (1 / 10) 0 (prefixState n) := by

  interval_cases n

  · exact prefix_step_0

  · exact prefix_step_1

  · exact prefix_step_2

  · exact prefix_step_3

  · exact prefix_step_4

  · exact prefix_step_5

  · exact prefix_step_6

  · exact prefix_step_7

  · exact prefix_step_8

  · exact prefix_step_9

  · exact prefix_step_10

  · exact prefix_step_11

  · exact prefix_step_12

  · exact prefix_step_13

  · exact prefix_step_14

  · exact prefix_step_15

  · exact prefix_step_16

  · exact prefix_step_17

  · exact prefix_step_18

  · exact prefix_step_19

  · exact prefix_step_20

  · exact prefix_step_21

  · exact prefix_step_22

  · exact prefix_step_23

  · exact prefix_step_24

  · exact prefix_step_25

theorem prefix_bounded (n : ℕ) (hn : n ≤ 26) : energy (prefixState n).1 (prefixState n).2 ≤ 5 := by

  interval_cases n <;> norm_num [prefixState, energy]

theorem prefix_entry : energy (prefixState 26).1 (prefixState 26).2 ≤ 1 / 10 := by

  norm_num [prefixState, energy]

theorem prefix_active (n : ℕ) (hn : n < 4) :

    1 < |SampledPD.control (Quantized.quantize (1 / 10000) (prefixState n).1)

      (Quantized.quantize (1 / 10000) (prefixState n).2)| ∧

    Quantized.input (1 / 10000) 1 (prefixState n).1 (prefixState n).2 = -1 := by

  interval_cases n <;> norm_num [prefixState, Quantized.input, Quantized.quantize, SampledPD.control, RobustPD.saturate]


/-- Every actual trajectory with this fixed, undisturbed prefix agrees with the
checked rational witness. Later inputs are arbitrary. -/
theorem run_prefix (h w : ℕ → ℝ)
    (hh : ∀ n < 26, h n = 1 / 10) (hw : ∀ n < 26, w n = 0) :
    ∀ n ≤ 26, run h w n = prefixState n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro hn
      have hn' : n < 26 := by omega
      rw [run, hh n hn', hw n hn', ih (by omega)]
      exact (prefix_step n hn').symm

/-- After the 26-step recovery episode, the controller accepts arbitrary future
sampling jitter and held disturbances within the existing robust envelope. -/
theorem tail_safe (h w : ℕ → ℝ)
    (hh : ∀ n < 26, h n = 1 / 10) (hw : ∀ n < 26, w n = 0)
    (hlo : ∀ n, 1 / 20 ≤ h (n + 26))
    (hhi : ∀ n, h (n + 26) ≤ 1 / 2)
    (hwind : ∀ n, |w (n + 26)| ≤ 1 / 4000) :
    ∀ n, energy (run h w (n + 26)).1 (run h w (n + 26)).2 ≤ 1 / 10 := by
  apply Quantized.safe_trajectory (fun n => h (n + 26))
    (fun n => (run h w (n + 26)).1) (fun n => (run h w (n + 26)).2)
    (fun n => w (n + 26)) hlo hhi hwind
  · rw [run_prefix h w hh hw 26 (by omega)]
    exact prefix_entry
  · intro n
    change (run h w ((n + 26) + 1)).1 = _
    rw [run]
    rfl
  · intro n
    change (run h w ((n + 26) + 1)).2 = _
    rw [run]
    rfl

/-- A bounded recovery episode with genuine active saturation: clipping is
active for the first four commands, all sample energies stay below 5, and from
sample 26 onward energy stays below 1/10. This certifies one initial condition
and a disturbance-free fixed-step prefix, not an entire saturated basin. -/
theorem recovery_guarantee (h w : ℕ → ℝ)
    (hh : ∀ n < 26, h n = 1 / 10) (hw : ∀ n < 26, w n = 0)
    (hlo : ∀ n, 1 / 20 ≤ h (n + 26))
    (hhi : ∀ n, h (n + 26) ≤ 1 / 2)
    (hwind : ∀ n, |w (n + 26)| ≤ 1 / 4000) :
    (∀ n < 4,
      1 < |SampledPD.control (Quantized.quantize (1 / 10000) (run h w n).1)
        (Quantized.quantize (1 / 10000) (run h w n).2)| ∧
      Quantized.input (1 / 10000) 1 (run h w n).1 (run h w n).2 = -1) ∧
    (∀ n, energy (run h w n).1 (run h w n).2 ≤ 5) ∧
    (∀ n, energy (run h w (n + 26)).1 (run h w (n + 26)).2 ≤ 1 / 10) := by
  have htail := tail_safe h w hh hw hlo hhi hwind
  refine ⟨?_, ?_, htail⟩
  · intro n hn
    rw [run_prefix h w hh hw n (by omega)]
    exact prefix_active n hn
  · intro n
    by_cases hn : n ≤ 26
    · rw [run_prefix h w hh hw n hn]
      exact prefix_bounded n hn
    · have he := htail (n - 26)
      have hindex : n - 26 + 26 = n := by omega
      rw [hindex] at he
      linarith

end LeanControls.SaturatedEntry
