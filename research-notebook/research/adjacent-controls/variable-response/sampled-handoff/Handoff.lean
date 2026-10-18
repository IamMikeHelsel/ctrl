module
public import Capture
public import RobustHold
@[expose] public section
noncomputable section
namespace LeanControls.SampledHoldHandoff
open Set VariableResponse SampledCapture RobustHold
open UncertainLag (State)

theorem coordinates_eq_raw (c : ℝ) (s : State) (i : Fin 3) :
    coordinates c s i = rawCoordinates s i-c := by
  fin_cases i <;> simp [coordinates, rawCoordinates] <;> ring

/-- A noisy sampled reading, bounded command delay and continuous full-state
handoff yield a persistent position tube under the actual robust hold law.
No exact zero-velocity detector is required. No state coordinate is reset.
This theorem does not assert eventual acceptance or a sampled hold implementation. -/
theorem delayed_reading_to_continuous_hold {d H : ℝ} (hd : 0 ≤ d)
    (hdmax : d ≤ 1/200) (hH : 0 ≤ H)
    {f g : ℝ → State} {j r w : ℝ → ℝ}
    (hf : IsCaptureTrajectory d f j)
    (hx : |f 0 0-7/50| ≤ 1/1000)
    (hv : |f 0 1-(-1/100)| ≤ 1/100)
    (ha : |f 0 2-(-117/100)| ≤ 1/20)
    (hab : ∀ t ∈ Icc 0 d, |f t 2| ≤ 2)
    (hjb : ∀ t ∈ Icc 0 d, |j t| ≤ 48)
    (hlink : g 0 = f d)
    (hg : IsTrajectory H r (fun t => command exampleCenter (g t)+w t) g)
    (hrlo : ∀ t ∈ Icc 0 H, 8 ≤ r t) (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 12)
    (hw : ∀ t ∈ Icc 0 H, |w t| ≤ 2*exampleRadius) :
    (∀ t ∈ Icc 0 d, f t 0 ≤ 3/20) ∧
    ∀ t ∈ Icc 0 H, 163/5000 ≤ g t 0 ∧ g t 0 ≤ 2873/20000 ∧
      |command exampleCenter (g t)+w t| ≤ 2 := by
  obtain ⟨hpath,hcap,_,_⟩ := concrete_capture hd hdmax hf hx hv ha hab hjb
  have hi : ∀ i, |coordinates exampleCenter (g 0) i| ≤ exampleRadius := by
    intro i
    rw [coordinates_eq_raw,hlink]
    exact hcap i
  have hb := actual_hold_bounds hH
    (by norm_num [exampleRadius] : 0 ≤ exampleRadius) hg hrlo hrhi hw hi
  refine ⟨hpath,?_⟩
  intro t ht
  have htube := abs_le.mp (hb t ht).1
  have hcmd := (hb t ht).2.2
  norm_num [exampleCenter,exampleRadius] at htube
  exact ⟨by linarith, by linarith,
    hcmd.trans (by norm_num [exampleRadius] : 26*exampleRadius ≤ 2)⟩

end LeanControls.SampledHoldHandoff
