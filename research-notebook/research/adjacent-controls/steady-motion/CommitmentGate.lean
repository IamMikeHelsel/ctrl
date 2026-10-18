module
public import Mathlib.Tactic
@[expose] public section
noncomputable section
namespace LeanControls.CommitmentGate

/-- Scalar proposal gate. This decides a target; it does not execute a motion. -/
def commit (c y H : ℝ) : ℝ := if H < |y-c| then y else c

def history (y : ℕ → ℝ) (c H : ℝ) : ℕ → ℝ
  | 0 => c
  | n+1 => commit (history y c H n) (y n) H

/-- Total variation along a finite list of accepted targets, including its anchor. -/
def variation (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, |f (i+1)-f i|

/-- Any actual change stores the new proposal and crosses the strict threshold. -/
theorem changed_target_is_proposal {c y H : ℝ} (h : commit c y H ≠ c) :
    commit c y H = y ∧ H < |y-c| := by
  by_cases hs : H < |y-c|
  · exact ⟨by simp [commit, hs], hs⟩
  · simp [commit, hs] at h

private theorem triangle (x y z : ℝ) : |x-z| ≤ |x-y|+|y-z| := by
  calc |x-z| = |(x-y)+(y-z)| := by congr 1; ring
       _ ≤ |x-y|+|y-z| := abs_add_le _ _

/-- A valid anchor and a valid new observation cannot differ by more than 2ε. -/
theorem noise_rejection {c y p ε H : ℝ}
    (hc : |c-p| ≤ ε) (hy : |y-p| ≤ ε) (hH : 2*ε ≤ H) :
    commit c y H = c := by
  have h := triangle y p c
  rw [abs_sub_comm p c] at h
  have hle : |y-c| ≤ H := by linarith
  simp [commit, not_lt.mpr hle]

/-- Any number of bounded noisy replans leave the initial valid anchor unchanged. -/
theorem fixed_target_history {y : ℕ → ℝ} {c p ε H : ℝ}
    (hc : |c-p| ≤ ε) (hy : ∀ k, |y k-p| ≤ ε) (hH : 2*ε ≤ H)
    (n : ℕ) : history y c H n = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [history, ih]
    exact noise_rejection hc (hy n) hH

/-- A distinguishable change passes this gate at its next valid observation.
A downstream segment-admission check may still reject the target. -/
theorem distinguishable_change {c y p ε H : ℝ}
    (hy : |y-p| ≤ ε) (hchange : H+ε < |p-c|) :
    commit c y H = y := by
  have h := triangle p y c
  rw [abs_sub_comm p y] at h
  have hpass : H < |y-c| := by linarith
  simp [commit, hpass]

/-- Sufficient response condition expressed relative to the old true target. -/
theorem true_step_response {c y pOld pNew ε H : ℝ}
    (hc : |c-pOld| ≤ ε) (hy : |y-pNew| ≤ ε)
    (hchange : H+2*ε < |pNew-pOld|) : commit c y H = y := by
  apply distinguishable_change hy
  have h := triangle pNew c pOld
  linarith

/-- A rejected observation gives a bounded target error, not physical tracking. -/
theorem rejected_target_error {c y p ε H : ℝ}
    (hy : |y-p| ≤ ε) (hreject : |y-c| ≤ H) : |c-p| ≤ H+ε := by
  have h := triangle c y p
  rw [abs_sub_comm c y] at h
  linarith

/-- The selected target is always within H+ε of the true target if H is nonnegative. -/
theorem selected_target_error {c y p ε H : ℝ}
    (hy : |y-p| ≤ ε) (hH : 0 ≤ H) : |commit c y H-p| ≤ H+ε := by
  by_cases h : H < |y-c|
  · simp only [commit, ite_eq_left h]
    linarith
  · simp only [commit, ite_eq_right h]
    exact rejected_target_error hy (le_of_not_gt h)

/-- One accepted-target step is no longer than true-target change plus two errors. -/
theorem step_variation_bound {c0 c1 p0 p1 ε : ℝ}
    (h0 : |c0-p0| ≤ ε) (h1 : |c1-p1| ≤ ε) :
    |c1-c0| ≤ |p1-p0|+2*ε := by
  have ha := triangle c1 p1 c0
  have hb := triangle p1 p0 c0
  rw [abs_sub_comm p0 c0] at hb
  linarith

/-- Each accepted step needs a nonzero true change when H exceeds 2ε. -/
theorem accepted_step_needs_change {c0 c1 p0 p1 ε H : ℝ}
    (h0 : |c0-p0| ≤ ε) (h1 : |c1-p1| ≤ ε) (hs : H < |c1-c0|) :
    H-2*ε < |p1-p0| := by
  have h := step_variation_bound h0 h1
  linarith

/-- Finite accepted histories obey a variation and switch-count contract.
Here p lists true targets at acceptance times; it need not be monotone or slow.
The first anchor must also be a valid observation. -/
theorem finite_variation_contract (c p : ℕ → ℝ) (n : ℕ) {ε H : ℝ}
    (he : 0 ≤ ε) (hH : 2*ε < H)
    (hvalid : ∀ i ≤ n, |c i-p i| ≤ ε)
    (hswitch : ∀ i < n, H < |c (i+1)-c i|) :
    (n : ℝ) ≤ variation p n / (H-2*ε) ∧
    variation c n ≤ H*variation p n / (H-2*ε) := by
  have hsum : variation c n ≤ variation p n + 2*ε*(n : ℝ) := by
    have hh := Finset.sum_le_sum (s := Finset.range n) (fun i hi =>
      step_variation_bound (hvalid i (by have := Finset.mem_range.mp hi; omega))
        (hvalid (i+1) (by have := Finset.mem_range.mp hi; omega)))
    simpa [variation, Finset.sum_add_distrib, mul_comm, mul_left_comm, mul_assoc] using hh
  have hcount : H*(n : ℝ) ≤ variation c n := by
    have hh := Finset.sum_le_sum (s := Finset.range n) (fun i hi =>
      le_of_lt (hswitch i (Finset.mem_range.mp hi)))
    simpa [variation, mul_comm] using hh
  have hδ : 0 < H-2*ε := by linarith
  constructor
  · apply (le_div_iff₀ hδ).2
    nlinarith
  · apply (le_div_iff₀ hδ).2
    have hH0 : 0 ≤ H := by linarith
    have ha := mul_le_mul_of_nonneg_left hsum hH0
    have hb := mul_le_mul_of_nonneg_left hcount (show 0 ≤ 2*ε by positivity)
    nlinarith

/-- The same observation is valid for both targets when they are at most 2ε apart.
This is an overlap witness; a general algorithm impossibility theorem is not claimed. -/
theorem indistinguishable_observation {δ ε : ℝ} (hδ : 0 ≤ δ) (he : δ ≤ 2*ε) :
    |δ/2-(0 : ℝ)| ≤ ε ∧ |δ/2-δ| ≤ ε := by
  constructor
  · rw [sub_zero, abs_of_nonneg (by positivity)]
    linarith
  · rw [abs_of_nonpos (by linarith)]
    linarith

/-- Recenter one raw hold coordinate without resetting the physical state.
The caller must separately check the new physical travel limits and input authority. -/
theorem reference_shift_bound {z cOld cNew R : ℝ} (hz : |z-cOld| ≤ R) :
    |z-cNew| ≤ R+|cNew-cOld| := by
  have h := triangle z cOld cNew
  rw [abs_sub_comm cOld cNew] at h
  linarith

/-- Proposal age consumes uncertainty whenever the true target moves.
The change bound must come from a separate target-speed or prediction model. -/
theorem stale_proposal_bound {y pThen pNow ε L age : ℝ}
    (hmodel : |y-pThen| ≤ ε) (hage : |pThen-pNow| ≤ L*age) :
    |y-pNow| ≤ ε+L*age := by
  have h := triangle y pThen pNow
  linarith

/-- Error to a true target follows only if a separate physical tracking bound exists. -/
theorem tracking_error_transfer {x c p R H ε : ℝ}
    (hphysical : |x-c| ≤ R) (htarget : |c-p| ≤ H+ε) :
    |x-p| ≤ R+H+ε := by
  have h := triangle x c p
  linarith

/-- Illustrative SI values: 0.5 mm uncertainty, 2 mm threshold.
The guarantee concerns target variation, not executed path length. -/
theorem concrete_contract (c p : ℕ → ℝ) (n : ℕ)
    (hvalid : ∀ i ≤ n, |c i-p i| ≤ (1/2000 : ℝ))
    (hswitch : ∀ i < n, (1/500 : ℝ) < |c (i+1)-c i|) :
    (n : ℝ) ≤ 1000*variation p n ∧ variation c n ≤ 2*variation p n := by
  have h := finite_variation_contract c p n (by norm_num : (0 : ℝ) ≤ 1/2000)
    (by norm_num : 2*(1/2000 : ℝ) < 1/500) hvalid hswitch
  norm_num at h
  constructor <;> nlinarith [h.1, h.2]
end LeanControls.CommitmentGate
