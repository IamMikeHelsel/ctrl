import domain_clock
noncomputable section
set_option autoImplicit false
namespace S02Binding
open Set LeanControls LeanControls.DigitalHold LeanControls.ConstructiveHold
open LeanControls.ConstructedHandoff LeanControls.DetectorBridge LeanControls.DetectorSampling
open S02Clock

/-- The bounded-latency adapter releases the unmodified source payloads on the
EXACT original clock. The returned Assembly supplies one switched physical
trajectory, both one-sided ODEs, pending prefix, schedule and safety together.
No arrival-triggered switch, timestamp renewal or counterfactual future reading
is substituted. Transport must deliver each genuine packet by its bound. -/
theorem buffered_source_handoff {f : ℝ → State} {rL qL rB qB : ℝ → ℝ}
    {m : ℕ → State} (ex : BrakingExecution f rL qL rB qB) (hm : Readings f m)
    (N : ℕ) (hN : 2≤N) {R δ : ℕ → ℝ} {ε : ℕ → State}
    (hr : ∀ n, 1≤n → 8≤R n ∧ R n≤12)
    (hd : ∀ n, 1≤n → |δ n|≤1/100)
    (he : ∀ n, |ε n 0|≤1/1000 ∧ |ε n 1|≤1/100 ∧ |ε n 2|≤1/20)
    (latency : ℕ → ℝ) (hb : ∀ n, 0≤latency n ∧ latency n≤h) :
    ∃ k, Assembly f rL qL rB qB m k N R δ ε ∧
      First (newReadings m (hold f m k N R δ ε) k ε) k ∧
      release latency k=grid k+h ∧
      (∀ j≤k, arrival latency j≤release latency k) ∧
      (∀ j<k, release latency j<release latency k) ∧
      (∀ t∈Icc 0 (release latency k), trajectory f m k N R δ ε t=f t) ∧
      (∀ j, j≤k+N → SensorBox (trajectory f m k N R δ ε (grid j))
        (newReadings m (hold f m k N R δ ε) k ε j)) ∧
      (∀ j, release latency (k+j)=grid k+h+grid j) ∧
      (∀ j, newReadings m (hold f m k N R δ ε) k ε (k+j)=
        (ConstructiveHold.schedule (m k) ε (hold f m k N R δ ε)).measurement j) := by
  obtain ⟨k,a⟩ := exists_assembly ex hm N hN hr hd he
  have hb' : ∀ n, latency n≤h := fun n => (hb n).2
  refine ⟨k,a,new_readings_first a.first,release_eq latency hb' k,?_,?_,?_,?_,?_,?_⟩
  · intro j hj
    exact prefix_available latency hb' hj
  · intro j hj
    exact release_strict latency hb' hj
  · rw [release_eq latency hb' k]
    exact a.prefix_eq
  · exact actual_readings a hm he
  · intro j
    rw [release_eq latency hb' (k+j),←(translated_clocks k j).1]
    ring
  · exact fun j => schedule_reading_link m (hold f m k N R δ ε) k j ε

#print axioms buffered_source_handoff
end S02Binding
