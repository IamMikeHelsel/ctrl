module
public import TraceExecution
@[expose] public section
noncomputable section
namespace LeanControls.FiniteHandoff
open UncertainLag UncertainTravel SamplingClock

/-- Samples through N depend only on commands and holds strictly before N. -/
theorem samples_congr_prefix {N : ℕ} (r : ℝ) (h e d H E D : ℕ → ℝ) (z : State)
    (hh : ∀ n<N, h n = H n) (he : ∀ n<N, e n = E n) (hd : ∀ n<N, d n = D n) :
    ∀ n≤N, samples r h e d z n = samples r H E D z n := by
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [samples_succ, samples_succ, hh n (by omega), he n (by omega),
      hd n (by omega), ih (by omega)]

/-- The invariant need hold only at sample N. Tail bounds start at N. -/
theorem samples_invariant_from {N : ℕ} {r : ℝ}
    (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10) (h e d : ℕ → ℝ) (z : State)
    (hlo : ∀ n, 0 ≤ h n) (hhi : ∀ n, N ≤ n → h n ≤ 1/5)
    (hb : ∀ n, N ≤ n → |e n| + |d n| ≤ 1/90)
    (hz : V (samples r h e d z N) ≤ 12) :
    ∀ n, N ≤ n → V (samples r h e d z n) ≤ 12 := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hz
  | succ k ih =>
    rw [Nat.add_succ, samples_succ]
    exact segment_invariant hrlo hrhi (hlo _) (hhi _ (by omega)) (hb _ (by omega)) (ih (by omega))

/-- Safe finite prefix plus an invariant tail gives every-real-time safety.
The feedback law and fixed rate are unchanged; prefix timing/error bounds may differ. -/
theorem actual_all_time_safe {N : ℕ} {r : ℝ}
    (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10) (h e d : ℕ → ℝ) (z : State)
    {hmin : ℝ} (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n)
    (hhi : ∀ n, N ≤ n → h n ≤ 1/5)
    (hb : ∀ n, N ≤ n → |e n| + |d n| ≤ 1/90)
    (hp : ∀ n<N, ∀ s, 0 ≤ s → s ≤ h n →
      |segment r s (samples r h e d z n) (e n) (d n) 0| ≤ 2)
    (hz : V (samples r h e d z N) ≤ 12)
    {f : ℝ → State} (hf : ExecutionUniqueness.IsExecution r h e d z f)
    {t : ℝ} (ht : 0 ≤ t) : |f t 0| ≤ 2 := by
  have hr : r ≠ 0 := ne_of_gt (by linarith)
  rw [ExecutionUniqueness.execution_eq_state r hr h e d z hmin0 hlo hf ht]
  obtain ⟨n, hnlo, hnhi⟩ := exists_segment h hmin0 hlo ht
  rw [UncertainExecution.state_on_interval r hr h e d z hmin0 hlo n ⟨hnlo, hnhi.le⟩]
  have hs0 : 0 ≤ t - sampleTime h n := sub_nonneg.mpr hnlo
  have hs1 : t - sampleTime h n ≤ h n := by rw [sampleTime_succ] at hnhi; linarith
  by_cases hn : n < N
  · exact hp n hn _ hs0 hs1
  · have hN : N ≤ n := by omega
    exact TravelGeometry.position_safe (segment_invariant hrlo hrhi hs0
      (hs1.trans (hhi n hN)) (hb n hN)
      (samples_invariant_from hrlo hrhi h e d z (fun n => hmin0.le.trans (hlo n))
        hhi hb hz n hN))

theorem exists_safe_execution {N : ℕ} {r : ℝ}
    (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10) (h e d : ℕ → ℝ) (z : State)
    {hmin : ℝ} (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n)
    (hhi : ∀ n, N ≤ n → h n ≤ 1/5)
    (hb : ∀ n, N ≤ n → |e n| + |d n| ≤ 1/90)
    (hp : ∀ n<N, ∀ s, 0 ≤ s → s ≤ h n →
      |segment r s (samples r h e d z n) (e n) (d n) 0| ≤ 2)
    (hz : V (samples r h e d z N) ≤ 12) :
    ∃ f : ℝ → State, ExecutionUniqueness.IsExecution r h e d z f ∧
      ∀ t, 0 ≤ t → |f t 0| ≤ 2 := by
  have hf := ExecutionUniqueness.constructed_isExecution r (ne_of_gt (by linarith))
    h e d z hmin0 hlo
  exact ⟨_, hf, fun t ht => actual_all_time_safe hrlo hrhi h e d z hmin0 hlo hhi hb hp hz hf ht⟩

end LeanControls.FiniteHandoff
#print axioms LeanControls.FiniteHandoff.samples_congr_prefix
#print axioms LeanControls.FiniteHandoff.samples_invariant_from
#print axioms LeanControls.FiniteHandoff.actual_all_time_safe
#print axioms LeanControls.FiniteHandoff.exists_safe_execution
