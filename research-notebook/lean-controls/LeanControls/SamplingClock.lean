module

public import LeanControls.DoubleIntegratorBridge

/-! Positive minimum sample intervals rule out accumulation in finite time.
The resulting coverage connects segment-wise certificates to every real t>=0. -/

@[expose] public section
noncomputable section
namespace LeanControls.SamplingClock

/-- Start time of sample n, with the first sample at real time zero. -/
def sampleTime (h : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, h k

@[simp]
theorem sampleTime_zero (h : ℕ → ℝ) : sampleTime h 0 = 0 := by
  simp [sampleTime]

theorem sampleTime_succ (h : ℕ → ℝ) (n : ℕ) :
    sampleTime h (n + 1) = sampleTime h n + h n := by
  simp [sampleTime, Finset.sum_range_succ]

/-- Sample times grow at least linearly in their sample index. -/
theorem sampleTime_lower (h : ℕ → ℝ) {hmin : ℝ} (hlo : ∀ n, hmin ≤ h n) (n : ℕ) :
    (n : ℝ) * hmin ≤ sampleTime h n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sampleTime_succ, Nat.cast_add, Nat.cast_one]
      linarith [hlo n]

/-- The positive minimum interval excludes infinitely many samples before any
finite real time. -/
theorem sampleTime_unbounded (h : ℕ → ℝ) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) (t : ℝ) :
    ∃ n, t < sampleTime h n := by
  obtain ⟨n, hn⟩ := exists_nat_gt (t / hmin)
  have hprod : t < (n : ℝ) * hmin := (div_lt_iff₀ hmin0).mp hn
  exact ⟨n, hprod.trans_le (sampleTime_lower h hlo n)⟩

/-- Half-open sample intervals cover every nonnegative real time. -/
theorem exists_segment (h : ℕ → ℝ) {hmin t : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) (ht : 0 ≤ t) :
    ∃ n, sampleTime h n ≤ t ∧ t < sampleTime h (n + 1) := by
  classical
  have hex := sampleTime_unbounded h hmin0 hlo t
  have hfirst : t < sampleTime h (Nat.find hex) := Nat.find_spec hex
  have hn0 : Nat.find hex ≠ 0 := by
    intro heq
    rw [heq, sampleTime_zero] at hfirst
    linarith
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · exact le_of_not_gt (Nat.find_min hex (by omega))
  · have heq : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rw [heq]
    exact hfirst

/-- The segment offset belongs to [0,h_n); the endpoint uses the next interval. -/
theorem exists_segment_offset (h : ℕ → ℝ) {hmin t : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) (ht : 0 ≤ t) :
    ∃ n s, t = sampleTime h n + s ∧ 0 ≤ s ∧ s < h n := by
  obtain ⟨n, hnlo, hnhi⟩ := exists_segment h hmin0 hlo ht
  refine ⟨n, t - sampleTime h n, by ring, sub_nonneg.mpr hnlo, ?_⟩
  rw [sampleTime_succ] at hnhi
  linarith

theorem sampleTime_strictMono (h : ℕ → ℝ) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) : StrictMono (sampleTime h) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [sampleTime_succ]
  linarith [hlo n]

/-- With positive durations, the containing half-open interval is unique. -/
theorem segment_unique (h : ℕ → ℝ) {hmin t : ℝ} {n m : ℕ}
    (hmin0 : 0 < hmin) (hlo : ∀ k, hmin ≤ h k)
    (hn : sampleTime h n ≤ t ∧ t < sampleTime h (n + 1))
    (hm : sampleTime h m ≤ t ∧ t < sampleTime h (m + 1)) : n = m := by
  have hmono := (sampleTime_strictMono h hmin0 hlo).monotone
  rcases lt_trichotomy n m with hnm | heq | hmn
  · have hh := hmono (show n + 1 ≤ m by omega)
    linarith [hn.2, hm.1]
  · exact heq
  · have hh := hmono (show m + 1 ≤ n by omega)
    linarith [hm.2, hn.1]

/-- Total selector; the fallback is irrelevant whenever the coverage hypotheses
hold. This is a mathematical definition, not an executable search over reals. -/
def segmentIndex (h : ℕ → ℝ) (t : ℝ) : ℕ := by
  classical
  exact if hex : ∃ n, sampleTime h n ≤ t ∧ t < sampleTime h (n + 1)
    then Nat.find hex else 0

theorem segmentIndex_spec (h : ℕ → ℝ) {hmin t : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) (ht : 0 ≤ t) :
    sampleTime h (segmentIndex h t) ≤ t ∧ t < sampleTime h (segmentIndex h t + 1) := by
  classical
  have hex := exists_segment h hmin0 hlo ht
  simp only [segmentIndex, dite_eq_left hex]
  exact Nat.find_spec hex

/-- A sample boundary belongs to its new interval, avoiding endpoint ambiguity. -/
theorem segmentIndex_at_sample (h : ℕ → ℝ) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) (n : ℕ) :
    segmentIndex h (sampleTime h n) = n := by
  have ht0 : 0 ≤ sampleTime h n :=
    (mul_nonneg (Nat.cast_nonneg n) hmin0.le).trans (sampleTime_lower h hlo n)
  apply segment_unique h hmin0 hlo (segmentIndex_spec h hmin0 hlo ht0)
  refine ⟨le_rfl, ?_⟩
  rw [sampleTime_succ]
  linarith [hlo n]

/-- Defined nominal held trajectory at real time t, assembled from its samples. -/
def nominalState (h x v : ℕ → ℝ) (t : ℝ) : ℝ × ℝ :=
  let n := segmentIndex h t
  let s := t - sampleTime h n
  (SampledPD.position s (x n) (v n), SampledPD.velocity s (x n) (v n))

/-- The assembled real-time trajectory agrees exactly with the supplied samples. -/
theorem nominalState_at_sample (h x v : ℕ → ℝ) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) (n : ℕ) :
    nominalState h x v (sampleTime h n) = (x n, v n) := by
  simp [nominalState, segmentIndex_at_sample h hmin0 hlo n,
    SampledPD.position_initial, SampledPD.velocity_initial]

/-- Every-real-time nominal energy bound. The power uses the actual containing
sample index; positive minimum timing guarantees that this index exists. -/
theorem nominal_energy_bound (h x v : ℕ → ℝ) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hminhi : hmin ≤ 33 / 50)
    (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ 33 / 50)
    (hx : ∀ n, x (n + 1) = SampledPD.position (h n) (x n) (v n))
    (hv : ∀ n, v (n + 1) = SampledPD.velocity (h n) (x n) (v n))
    {t : ℝ} (ht : 0 ≤ t) :
    PD.energy (nominalState h x v t).1 (nominalState h x v t).2 ≤
      (1 - hmin / 600) ^ (segmentIndex h t) * PD.energy (x 0) (v 0) := by
  obtain ⟨htlo, hthi⟩ := segmentIndex_spec h hmin0 hlo ht
  rw [sampleTime_succ] at hthi
  exact DoubleIntegratorBridge.wide_trajectory_intersample h x v hmin0.le hminhi
    hlo hhi hx hv (segmentIndex h t) (sub_nonneg.mpr htlo) (by linarith)

/-- In particular, the nominal trajectory never exceeds its initial energy at
any real t>=0. This is not pairwise monotonicity between arbitrary real times. -/
theorem nominal_energy_nonexpansion (h x v : ℕ → ℝ) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hminhi : hmin ≤ 33 / 50)
    (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ 33 / 50)
    (hx : ∀ n, x (n + 1) = SampledPD.position (h n) (x n) (v n))
    (hv : ∀ n, v (n + 1) = SampledPD.velocity (h n) (x n) (v n))
    {t : ℝ} (ht : 0 ≤ t) :
    PD.energy (nominalState h x v t).1 (nominalState h x v t).2 ≤ PD.energy (x 0) (v 0) := by
  have hb := nominal_energy_bound h x v hmin0 hminhi hlo hhi hx hv ht
  have hpow : (1 - hmin / 600) ^ segmentIndex h t ≤ 1 :=
    pow_le_one₀ (by linarith) (by linarith)
  have hm := mul_le_mul_of_nonneg_right hpow (PD.energy_nonneg (x 0) (v 0))
  simpa using hb.trans hm

end LeanControls.SamplingClock
