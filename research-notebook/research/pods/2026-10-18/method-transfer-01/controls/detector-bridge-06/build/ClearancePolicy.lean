module
public import WeightedEntry
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LeanControls.ClearancePolicy
open DigitalHold WeightedEntry

def max3 (f : Fin 3 → ℝ) : ℝ := max (f 0) (max (f 1) (f 2))
theorem le_max3 (f : Fin 3 → ℝ) (i : Fin 3) : f i ≤ max3 f := by
  fin_cases i <;> simp [max3]
theorem max3_le {f : Fin 3 → ℝ} {B : ℝ} (h : ∀ i, f i ≤ B) : max3 f ≤ B :=
  max_le (h 0) (max_le (h 1) (h 2))

def offsets (m : State) : State := ![m 0,m 0+m 1/4,m 0+m 1/2+m 2/16]
def error : State := ![101533/100000000,368033/100000000,1042283/100000000]
def pair (m : State) (i j : Fin 3) : ℝ :=
  (offsets m i-offsets m j+error i+error j)/(weight i+weight j)
def policyRadius (m : State) : ℝ := max target (max3 (fun i => max3 (pair m i)))
def center (m : State) : ℝ := max3 (fun i => offsets m i+error i-weight i*policyRadius m)
def Guard (m : State) : Prop := m 0 ≤ 143/1000 ∧ |m 1| ≤ 561/50000 ∧
  -127/100 ≤ m 2 ∧ m 2 ≤ -1/5

theorem radius_floor (m : State) : target ≤ policyRadius m := le_max_left _ _
theorem pair_le_radius (m : State) (i j : Fin 3) : pair m i j ≤ policyRadius m :=
  (le_max3 (pair m i) j).trans ((le_max3 (fun i => max3 (pair m i)) i).trans (le_max_right _ _))

theorem feasible (m : State) (i : Fin 3) :
    |offsets m i-center m|+error i ≤ weight i*policyRadius m := by
  have hlo : offsets m i+error i-weight i*policyRadius m ≤ center m := le_max3 (fun j => offsets m j+error j-weight j*policyRadius m) i
  have hhi : center m ≤ offsets m i-error i+weight i*policyRadius m := by
    apply max3_le
    intro j
    have hp := pair_le_radius m j i
    have hw := add_pos (weight_pos j) (weight_pos i)
    rw [pair,div_le_iff₀ hw] at hp
    nlinarith
  have hh : |offsets m i-center m| ≤ weight i*policyRadius m-error i :=
    abs_le.mpr ⟨by linarith,by linarith⟩
  linarith

theorem radius_upper {m : State} (hg : Guard m) : policyRadius m ≤ 2407079/50250000 := by
  have hv := abs_le.mp hg.2.1
  obtain ⟨hx,hv',ha,hahi⟩ := hg
  apply max_le
  · norm_num [target]
  · apply max3_le; intro i; apply max3_le; intro j
    fin_cases i <;> fin_cases j <;> norm_num [pair,offsets,error,weight] <;> linarith

theorem weighted_inside_old_cube {m : State} (hg : Guard m) (i : Fin 3) :
    weight i*policyRadius m < radius := by
  have hK := radius_upper hg
  fin_cases i <;> norm_num [weight,radius] <;> linarith

/-- An exact finite-affine certificate over the full continuous guard.
No numerical sample or corner-only premise is used. -/
theorem forward_upper {m : State} (hg : Guard m) :
    center m+(51/50)*policyRadius m ≤ 3013722449/20100000000 := by
  have hv := abs_le.mp hg.2.1
  obtain ⟨hx,hv',ha,hahi⟩ := hg
  have hb (i : Fin 3) : offsets m i+error i+((51/50)-weight i)*policyRadius m ≤
      3013722449/20100000000 := by
    fin_cases i
    · norm_num [offsets,error,weight]; linarith
    · have hK : policyRadius m ≤ 100*(3013722449/20100000000-offsets m 1-error 1) := by
        apply max_le
        · norm_num [target,offsets,error]; linarith
        · apply max3_le; intro i; apply max3_le; intro j
          fin_cases i <;> fin_cases j <;> norm_num [pair,offsets,error,weight] <;> linarith
      norm_num [weight] at *; linarith
    · have hK : policyRadius m ≤ 50*(3013722449/20100000000-offsets m 2-error 2) := by
        apply max_le
        · norm_num [target,offsets,error]; linarith
        · apply max3_le; intro i; apply max3_le; intro j
          fin_cases i <;> fin_cases j <;> norm_num [pair,offsets,error,weight] <;> linarith
      norm_num [weight] at *; linarith
  have hh : center m ≤ 3013722449/20100000000-(51/50)*policyRadius m := by
    apply max3_le; intro i
    have h := hb i
    nlinarith
  linarith

theorem clearance_margin {m : State} (hg : Guard m) :
    center m+(51/50)*policyRadius m ≤ 3/20-1277551/20100000000 := by
  convert forward_upper hg using 1 <;> norm_num

def nominal : State := ![7/50,-1/100,-117/100]
theorem nominal_policy : Guard nominal ∧ policyRadius nominal=9/200 ∧
    center nominal=9573033/100000000 ∧
    center nominal+(51/50)*policyRadius nominal=14163033/100000000 ∧
    command (center nominal) nominal=3635533/12500000 := by
  norm_num [Guard,nominal,policyRadius,max3,pair,offsets,error,weight,target,center,command]

theorem wider_speed_fails :
    3/20 < center ![143/1000,1/50,-127/100]+(51/50)*policyRadius ![143/1000,1/50,-127/100] := by
  norm_num [policyRadius,max3,pair,offsets,error,weight,target,center]

/-- Fixed-center baseline uses the SAME interval errors and weights. -/
def fixedRadius (m : State) (c : ℝ) : ℝ :=
  max target (max3 (fun i => (|offsets m i-c|+error i)/weight i))

theorem fair_nominal_baseline :
    fixedRadius nominal (323/3200)=4948533/100000000 ∧
    (323/3200)+(51/50)*fixedRadius nominal (323/3200)=757062683/5000000000 ∧
    3/20 < (323/3200)+(51/50)*fixedRadius nominal (323/3200) := by
  norm_num [fixedRadius,max3,nominal,offsets,error,weight,target]

/-- Exact rectangle corners; the full-guard theorem is proved separately. -/
theorem exact_corners :
    policyRadius ![143/1000,-561/50000,-127/100]=2407079/50250000 ∧
    center ![143/1000,-561/50000,-127/100]+(51/50)*policyRadius ![143/1000,-561/50000,-127/100]=2901522449/20100000000 ∧
    policyRadius ![143/1000,-561/50000,-1/5]=9/200 ∧
    center ![143/1000,-561/50000,-1/5]+(51/50)*policyRadius ![143/1000,-561/50000,-1/5]=14432533/100000000 ∧
    policyRadius ![143/1000,561/50000,-127/100]=2266829/50250000 ∧
    center ![143/1000,561/50000,-127/100]+(51/50)*policyRadius ![143/1000,561/50000,-127/100]=3013722449/20100000000 ∧
    policyRadius ![143/1000,561/50000,-1/5]=9/200 ∧
    center ![143/1000,561/50000,-1/5]+(51/50)*policyRadius ![143/1000,561/50000,-1/5]=14993533/100000000 := by
  norm_num [policyRadius,center,max3,pair,offsets,error,weight,target]

theorem equilibrium_reading_rejected (c : ℝ) : ¬ Guard ![c,0,0] := by
  norm_num [Guard]

end LeanControls.ClearancePolicy
