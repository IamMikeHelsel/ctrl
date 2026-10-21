module
public import ClearancePolicy
@[expose] public section
noncomputable section
namespace S11
open LeanControls.DigitalHold LeanControls.WeightedEntry LeanControls.ClearancePolicy

theorem weighted_tolerance_bounds {c K : ℝ} {s : State}
    (hz : ∀ i, |coordinates c s i| ≤ weight i*K) :
    |s 0-c| ≤ (51/50)*K ∧ |s 1| ≤ (203/25)*K ∧
    |s 2| ≤ (1616/25)*K ∧ |command c s| ≤ (606/25)*K := by
  have h0 := abs_le.mp (hz 0)
  have h1 := abs_le.mp (hz 1)
  have h2 := abs_le.mp (hz 2)
  norm_num [coordinates,weight] at h0 h1 h2
  dsimp [command]
  exact ⟨abs_le.mpr ⟨by linarith,by linarith⟩,
    abs_le.mpr ⟨by linarith,by linarith⟩,
    abs_le.mpr ⟨by linarith,by linarith⟩,
    abs_le.mpr ⟨by linarith,by linarith⟩⟩

/-- Center feasibility for the exact C5 propagated observation intervals,
with an additional two-sided physical-position reserve. -/
theorem center_admission_iff (m : State) (K L U c : ℝ) :
    ((∀ i, |offsets m i-c|+error i ≤ weight i*K) ∧
      L+(51/50)*K ≤ c ∧ c ≤ U-(51/50)*K) ↔
    ((∀ i, offsets m i+error i-weight i*K ≤ c ∧
             c ≤ offsets m i-error i+weight i*K) ∧
      L+(51/50)*K ≤ c ∧ c ≤ U-(51/50)*K) := by
  constructor
  · rintro ⟨h,hl,hu⟩
    refine ⟨?_,hl,hu⟩
    intro i
    have hh : |offsets m i-c| ≤ weight i*K-error i := by linarith [h i]
    have ha := abs_le.mp hh
    constructor <;> linarith
  · rintro ⟨h,hl,hu⟩
    refine ⟨?_,hl,hu⟩
    intro i
    have hh := h i
    have ha : |offsets m i-c| ≤ weight i*K-error i :=
      abs_le.mpr ⟨by linarith,by linarith⟩
    linarith

theorem two_sided_terminal {L U c K : ℝ} {s : State}
    (hz : ∀ i, |coordinates c s i| ≤ weight i*K)
    (hl : L+(51/50)*K ≤ c) (hu : c ≤ U-(51/50)*K) :
    L ≤ s 0 ∧ s 0 ≤ U := by
  have h := abs_le.mp (weighted_tolerance_bounds hz).1
  constructor <;> linarith

/-- Exact finite interval-intersection admission, including both travel sides.
The candidate is the leftmost feasible center; no physical state reset is implied. -/
theorem exists_center_iff (m : State) (K L U : ℝ) :
    (∃ c, (∀ i, |offsets m i-c|+error i ≤ weight i*K) ∧
      L+(51/50)*K ≤ c ∧ c ≤ U-(51/50)*K) ↔
    let lower := max (L+(51/50)*K)
      (max3 (fun i => offsets m i+error i-weight i*K))
    (∀ i, lower ≤ offsets m i-error i+weight i*K) ∧
      lower ≤ U-(51/50)*K := by
  dsimp only
  constructor
  · rintro ⟨c,h⟩
    have hc := (center_admission_iff m K L U c).mp h
    have hb : max (L+(51/50)*K)
        (max3 (fun i => offsets m i+error i-weight i*K)) ≤ c := by
      exact max_le hc.2.1 (max3_le (fun i => (hc.1 i).1))
    exact ⟨fun i => hb.trans (hc.1 i).2, hb.trans hc.2.2⟩
  · intro h
    refine ⟨max (L+(51/50)*K) (max3 (fun i => offsets m i+error i-weight i*K)), ?_⟩
    apply (center_admission_iff m K L U _).mpr
    refine ⟨?_, le_max_left _ _, h.2⟩
    intro i
    exact ⟨(le_max3 (fun j => offsets m j+error j-weight j*K) i).trans
      (le_max_right _ _), h.1 i⟩

/-- Current policy floor cannot establish the proposed 1mm/s box certificate.
This is failure of this certificate, not impossibility of the actual trajectory. -/
theorem source_floor_prevents_millimeter_speed (K : ℝ)
    (hk : target ≤ K) : ¬ ((203/25)*K ≤ (1/1000 : ℝ)) := by
  norm_num [target] at hk
  linarith

/-- The C8 admitted braking witness continued without a hold switch. -/
theorem continued_braking_witness :
    (39/100 : ℝ)-(6/5)*(13/40)=0 ∧
    (1/1000 : ℝ)+(39/100)*(13/40)-(3/5)*(13/40)^2=103/1600 ∧
    (1/1000 : ℝ)+(39/100)*(2/3)-(3/5)*(2/3)^2= -17/3000 ∧
    (-17/3000 : ℝ)<0 := by norm_num

#print axioms weighted_tolerance_bounds
#print axioms center_admission_iff
#print axioms two_sided_terminal
#print axioms exists_center_iff
#print axioms source_floor_prevents_millimeter_speed
#print axioms continued_braking_witness
end S11
