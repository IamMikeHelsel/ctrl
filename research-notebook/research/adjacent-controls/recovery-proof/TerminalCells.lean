module
public import TerminalBase
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
@[expose] public section
noncomputable section
namespace LeanControls.RecoveryTerminal
open Matrix BernsteinCertificate
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem exp_point_0 : ((324651/1000000:ℚ):ℝ) ≤ Real.exp ((-9/8:ℚ):ℝ) ∧
    Real.exp ((-9/8:ℚ):ℝ) ≤ ((324653/1000000:ℚ):ℝ) := by
  apply exp_point (a := ((284891/500000:ℚ):ℝ)) (b := ((569783/1000000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_1 : ((2577/8000:ℚ):ℝ) ≤ Real.exp ((-145/128:ℚ):ℝ) ∧
    Real.exp ((-145/128:ℚ):ℝ) ≤ ((322127/1000000:ℚ):ℝ) := by
  apply exp_point (a := ((567561/1000000:ℚ):ℝ)) (b := ((283781/500000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_2 : ((159809/500000:ℚ):ℝ) ≤ Real.exp ((-73/64:ℚ):ℝ) ∧
    Real.exp ((-73/64:ℚ):ℝ) ≤ ((15981/50000:ℚ):ℝ) := by
  apply exp_point (a := ((141337/250000:ℚ):ℝ)) (b := ((565349/1000000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_3 : ((317131/1000000:ℚ):ℝ) ≤ Real.exp ((-147/128:ℚ):ℝ) ∧
    Real.exp ((-147/128:ℚ):ℝ) ≤ ((317133/1000000:ℚ):ℝ) := by
  apply exp_point (a := ((70393/125000:ℚ):ℝ)) (b := ((112629/200000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_4 : ((314663/1000000:ℚ):ℝ) ≤ Real.exp ((-37/32:ℚ):ℝ) ∧
    Real.exp ((-37/32:ℚ):ℝ) ≤ ((62933/200000:ℚ):ℝ) := by
  apply exp_point (a := ((560949/1000000:ℚ):ℝ)) (b := ((11219/20000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_5 : ((156107/500000:ℚ):ℝ) ≤ Real.exp ((-149/128:ℚ):ℝ) ∧
    Real.exp ((-149/128:ℚ):ℝ) ≤ ((312217/1000000:ℚ):ℝ) := by
  apply exp_point (a := ((279381/500000:ℚ):ℝ)) (b := ((558763/1000000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_6 : ((38723/125000:ℚ):ℝ) ≤ Real.exp ((-75/64:ℚ):ℝ) ∧
    Real.exp ((-75/64:ℚ):ℝ) ≤ ((154893/500000:ℚ):ℝ) := by
  apply exp_point (a := ((556583/1000000:ℚ):ℝ)) (b := ((69573/125000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_7 : ((307373/1000000:ℚ):ℝ) ≤ Real.exp ((-151/128:ℚ):ℝ) ∧
    Real.exp ((-151/128:ℚ):ℝ) ≤ ((2459/8000:ℚ):ℝ) := by
  apply exp_point (a := ((554413/1000000:ℚ):ℝ)) (b := ((277207/500000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_8 : ((152491/500000:ℚ):ℝ) ≤ Real.exp ((-19/16:ℚ):ℝ) ∧
    Real.exp ((-19/16:ℚ):ℝ) ≤ ((38123/125000:ℚ):ℝ) := by
  apply exp_point (a := ((138063/250000:ℚ):ℝ)) (b := ((552253/1000000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_9 : ((18913/62500:ℚ):ℝ) ≤ Real.exp ((-153/128:ℚ):ℝ) ∧
    Real.exp ((-153/128:ℚ):ℝ) ≤ ((302611/1000000:ℚ):ℝ) := by
  apply exp_point (a := ((550099/1000000:ℚ):ℝ)) (b := ((5501/10000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_10 : ((300253/1000000:ℚ):ℝ) ≤ Real.exp ((-77/64:ℚ):ℝ) ∧
    Real.exp ((-77/64:ℚ):ℝ) ≤ ((60051/200000:ℚ):ℝ) := by
  apply exp_point (a := ((273977/500000:ℚ):ℝ)) (b := ((109591/200000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_11 : ((297917/1000000:ℚ):ℝ) ≤ Real.exp ((-155/128:ℚ):ℝ) ∧
    Real.exp ((-155/128:ℚ):ℝ) ≤ ((297919/1000000:ℚ):ℝ) := by
  apply exp_point (a := ((272909/500000:ℚ):ℝ)) (b := ((545819/1000000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_12 : ((147799/500000:ℚ):ℝ) ≤ Real.exp ((-39/32:ℚ):ℝ) ∧
    Real.exp ((-39/32:ℚ):ℝ) ≤ ((739/2500:ℚ):ℝ) := by
  apply exp_point (a := ((54369/100000:ℚ):ℝ)) (b := ((543691/1000000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_13 : ((146649/500000:ℚ):ℝ) ≤ Real.exp ((-157/128:ℚ):ℝ) ∧
    Real.exp ((-157/128:ℚ):ℝ) ≤ ((2933/10000:ℚ):ℝ) := by
  apply exp_point (a := ((54157/100000:ℚ):ℝ)) (b := ((541571/1000000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_14 : ((36377/125000:ℚ):ℝ) ≤ Real.exp ((-79/64:ℚ):ℝ) ∧
    Real.exp ((-79/64:ℚ):ℝ) ≤ ((145509/500000:ℚ):ℝ) := by
  apply exp_point (a := ((539459/1000000:ℚ):ℝ)) (b := ((26973/50000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_15 : ((288751/1000000:ℚ):ℝ) ≤ Real.exp ((-159/128:ℚ):ℝ) ∧
    Real.exp ((-159/128:ℚ):ℝ) ≤ ((288753/1000000:ℚ):ℝ) := by
  apply exp_point (a := ((134339/250000:ℚ):ℝ)) (b := ((537357/1000000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_16 : ((35813/125000:ℚ):ℝ) ≤ Real.exp ((-5/4:ℚ):ℝ) ∧
    Real.exp ((-5/4:ℚ):ℝ) ≤ ((143253/500000:ℚ):ℝ) := by
  apply exp_point (a := ((535261/1000000:ℚ):ℝ)) (b := ((267631/500000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_17 : ((142137/500000:ℚ):ℝ) ≤ Real.exp ((-161/128:ℚ):ℝ) ∧
    Real.exp ((-161/128:ℚ):ℝ) ≤ ((71069/250000:ℚ):ℝ) := by
  apply exp_point (a := ((266587/500000:ℚ):ℝ)) (b := ((21327/40000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_18 : ((282061/1000000:ℚ):ℝ) ≤ Real.exp ((-81/64:ℚ):ℝ) ∧
    Real.exp ((-81/64:ℚ):ℝ) ≤ ((282063/1000000:ℚ):ℝ) := by
  apply exp_point (a := ((106219/200000:ℚ):ℝ)) (b := ((66387/125000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_19 : ((279867/1000000:ℚ):ℝ) ≤ Real.exp ((-163/128:ℚ):ℝ) ∧
    Real.exp ((-163/128:ℚ):ℝ) ≤ ((279869/1000000:ℚ):ℝ) := by
  apply exp_point (a := ((21161/40000:ℚ):ℝ)) (b := ((264513/500000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_20 : ((34711/125000:ℚ):ℝ) ≤ Real.exp ((-41/32:ℚ):ℝ) ∧
    Real.exp ((-41/32:ℚ):ℝ) ≤ ((277691/1000000:ℚ):ℝ) := by
  apply exp_point (a := ((263481/500000:ℚ):ℝ)) (b := ((526963/1000000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_21 : ((34441/125000:ℚ):ℝ) ≤ Real.exp ((-165/128:ℚ):ℝ) ∧
    Real.exp ((-165/128:ℚ):ℝ) ≤ ((27553/100000:ℚ):ℝ) := by
  apply exp_point (a := ((131227/250000:ℚ):ℝ)) (b := ((524909/1000000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_22 : ((34173/125000:ℚ):ℝ) ≤ Real.exp ((-83/64:ℚ):ℝ) ∧
    Real.exp ((-83/64:ℚ):ℝ) ≤ ((136693/500000:ℚ):ℝ) := by
  apply exp_point (a := ((261431/500000:ℚ):ℝ)) (b := ((522863/1000000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_23 : ((33907/125000:ℚ):ℝ) ≤ Real.exp ((-167/128:ℚ):ℝ) ∧
    Real.exp ((-167/128:ℚ):ℝ) ≤ ((135629/500000:ℚ):ℝ) := by
  apply exp_point (a := ((520823/1000000:ℚ):ℝ)) (b := ((65103/125000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_24 : ((134573/500000:ℚ):ℝ) ≤ Real.exp ((-21/16:ℚ):ℝ) ∧
    Real.exp ((-21/16:ℚ):ℝ) ≤ ((67287/250000:ℚ):ℝ) := by
  apply exp_point (a := ((518793/1000000:ℚ):ℝ)) (b := ((259397/500000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_25 : ((267051/1000000:ℚ):ℝ) ≤ Real.exp ((-169/128:ℚ):ℝ) ∧
    Real.exp ((-169/128:ℚ):ℝ) ≤ ((267053/1000000:ℚ):ℝ) := by
  apply exp_point (a := ((51677/100000:ℚ):ℝ)) (b := ((516771/1000000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_26 : ((66243/250000:ℚ):ℝ) ≤ Real.exp ((-85/64:ℚ):ℝ) ∧
    Real.exp ((-85/64:ℚ):ℝ) ≤ ((132487/500000:ℚ):ℝ) := by
  apply exp_point (a := ((102951/200000:ℚ):ℝ)) (b := ((128689/250000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_27 : ((262911/1000000:ℚ):ℝ) ≤ Real.exp ((-171/128:ℚ):ℝ) ∧
    Real.exp ((-171/128:ℚ):ℝ) ≤ ((262913/1000000:ℚ):ℝ) := by
  apply exp_point (a := ((512749/1000000:ℚ):ℝ)) (b := ((2051/4000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_28 : ((52173/200000:ℚ):ℝ) ≤ Real.exp ((-43/32:ℚ):ℝ) ∧
    Real.exp ((-43/32:ℚ):ℝ) ≤ ((260867/1000000:ℚ):ℝ) := by
  apply exp_point (a := ((2043/4000:ℚ):ℝ)) (b := ((510751/1000000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_29 : ((129417/500000:ℚ):ℝ) ≤ Real.exp ((-173/128:ℚ):ℝ) ∧
    Real.exp ((-173/128:ℚ):ℝ) ≤ ((64709/250000:ℚ):ℝ) := by
  apply exp_point (a := ((254379/500000:ℚ):ℝ)) (b := ((508759/1000000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_30 : ((12841/50000:ℚ):ℝ) ≤ Real.exp ((-87/64:ℚ):ℝ) ∧
    Real.exp ((-87/64:ℚ):ℝ) ≤ ((128411/500000:ℚ):ℝ) := by
  apply exp_point (a := ((20271/40000:ℚ):ℝ)) (b := ((63347/125000:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_31 : ((127411/500000:ℚ):ℝ) ≤ Real.exp ((-175/128:ℚ):ℝ) ∧
    Real.exp ((-175/128:ℚ):ℝ) ≤ ((31853/125000:ℚ):ℝ) := by
  apply exp_point (a := ((504799/1000000:ℚ):ℝ)) (b := ((631/1250:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem exp_point_32 : ((252839/1000000:ℚ):ℝ) ≤ Real.exp ((-11/8:ℚ):ℝ) ∧
    Real.exp ((-11/8:ℚ):ℝ) ≤ ((252841/1000000:ℚ):ℝ) := by
  apply exp_point (a := ((502831/1000000:ℚ):ℝ)) (b := ((31427/62500:ℚ):ℝ))
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]

theorem held_terminal_coordinates {r : ℝ} (hr : 0 < r) (z : Fin 3 → ℝ) :
    UncertainLag.heldSegment r (5/4) z (-1) =
      ![z 0 + z 1*1.25 - 0.78125 + (z 2+1)*r⁻¹*(1.25-(1-Real.exp (-r*(5/4)))*r⁻¹),
        z 1-1.25+(z 2+1)*(1-Real.exp (-r*(5/4)))*r⁻¹,
        -1+(z 2+1)*Real.exp (-r*(5/4))] := by
  have hn := ne_of_gt hr
  ext i
  fin_cases i <;> dsimp [UncertainLag.heldSegment, UncertainLag.heldSolution] <;>
    field_simp <;> ring

theorem cell_0 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((9/10:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((29/32:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((2577/8000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_1.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((324653/1000000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_0.2
  have hirlo : ((32/29:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((10/9:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((9/10:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_1 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((29/32:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((73/80:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((159809/500000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_2.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((322127/1000000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_1.2
  have hirlo : ((80/73:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((32/29:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((29/32:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_2 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((73/80:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((147/160:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((317131/1000000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_3.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((15981/50000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_2.2
  have hirlo : ((160/147:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((80/73:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((73/80:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_3 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((147/160:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((37/40:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((314663/1000000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_4.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((317133/1000000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_3.2
  have hirlo : ((40/37:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((160/147:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((147/160:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_4 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((37/40:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((149/160:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((156107/500000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_5.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((62933/200000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_4.2
  have hirlo : ((160/149:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((40/37:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((37/40:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_5 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((149/160:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((15/16:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((38723/125000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_6.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((312217/1000000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_5.2
  have hirlo : ((16/15:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((160/149:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((149/160:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_6 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((15/16:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((151/160:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((307373/1000000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_7.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((154893/500000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_6.2
  have hirlo : ((160/151:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((16/15:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((15/16:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_7 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((151/160:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((19/20:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((152491/500000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_8.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((2459/8000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_7.2
  have hirlo : ((20/19:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((160/151:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((151/160:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_8 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((19/20:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((153/160:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((18913/62500:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_9.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((38123/125000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_8.2
  have hirlo : ((160/153:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((20/19:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((19/20:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_9 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((153/160:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((77/80:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((300253/1000000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_10.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((302611/1000000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_9.2
  have hirlo : ((80/77:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((160/153:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((153/160:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_10 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((77/80:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((31/32:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((297917/1000000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_11.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((60051/200000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_10.2
  have hirlo : ((32/31:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((80/77:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((77/80:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_11 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((31/32:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((39/40:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((147799/500000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_12.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((297919/1000000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_11.2
  have hirlo : ((40/39:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((32/31:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((31/32:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_12 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((39/40:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((157/160:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((146649/500000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_13.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((739/2500:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_12.2
  have hirlo : ((160/157:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((40/39:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((39/40:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_13 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((157/160:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((79/80:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((36377/125000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_14.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((2933/10000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_13.2
  have hirlo : ((80/79:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((160/157:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((157/160:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_14 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((79/80:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((159/160:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((288751/1000000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_15.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((145509/500000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_14.2
  have hirlo : ((160/159:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((80/79:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((79/80:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_15 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((159/160:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((1/1:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((35813/125000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_16.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((288753/1000000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_15.2
  have hirlo : ((1/1:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((160/159:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((159/160:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_16 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((1/1:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((161/160:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((142137/500000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_17.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((143253/500000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_16.2
  have hirlo : ((160/161:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((1/1:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((1/1:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_17 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((161/160:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((81/80:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((282061/1000000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_18.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((71069/250000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_17.2
  have hirlo : ((80/81:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((160/161:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((161/160:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_18 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((81/80:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((163/160:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((279867/1000000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_19.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((282063/1000000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_18.2
  have hirlo : ((160/163:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((80/81:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((81/80:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_19 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((163/160:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((41/40:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((34711/125000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_20.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((279869/1000000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_19.2
  have hirlo : ((40/41:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((160/163:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((163/160:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_20 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((41/40:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((33/32:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((34441/125000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_21.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((277691/1000000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_20.2
  have hirlo : ((32/33:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((40/41:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((41/40:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_21 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((33/32:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((83/80:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((34173/125000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_22.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((27553/100000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_21.2
  have hirlo : ((80/83:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((32/33:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((33/32:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_22 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((83/80:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((167/160:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((33907/125000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_23.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((136693/500000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_22.2
  have hirlo : ((160/167:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((80/83:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((83/80:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_23 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((167/160:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((21/20:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((134573/500000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_24.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((135629/500000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_23.2
  have hirlo : ((20/21:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((160/167:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((167/160:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_24 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((21/20:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((169/160:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((267051/1000000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_25.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((67287/250000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_24.2
  have hirlo : ((160/169:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((20/21:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((21/20:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_25 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((169/160:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((17/16:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((66243/250000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_26.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((267053/1000000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_25.2
  have hirlo : ((16/17:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((160/169:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((169/160:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_26 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((17/16:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((171/160:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((262911/1000000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_27.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((132487/500000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_26.2
  have hirlo : ((160/171:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((16/17:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((17/16:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_27 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((171/160:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((43/40:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((52173/200000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_28.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((262913/1000000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_27.2
  have hirlo : ((40/43:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((160/171:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((171/160:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_28 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((43/40:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((173/160:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((129417/500000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_29.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((260867/1000000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_28.2
  have hirlo : ((160/173:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((40/43:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((43/40:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_29 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((173/160:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((87/80:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((12841/50000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_30.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((64709/250000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_29.2
  have hirlo : ((80/87:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((160/173:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((173/160:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_30 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((87/80:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((35/32:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((127411/500000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_31.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((128411/500000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_30.2
  have hirlo : ((32/35:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((80/87:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((87/80:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem cell_31 {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : ((35/32:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((11/10:ℚ):ℝ))
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : ((252839/1000000:ℚ):ℝ) ≤ Real.exp (-r*(5/4)) :=
    exp_point_32.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ ((31853/125000:ℚ):ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_31.2
  have hirlo : ((10/11:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((32/35:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((35/32:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]

theorem terminal_energy {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10)
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by

  by_cases h0 : r ≤ ((29/32:ℚ):ℝ)

  · exact cell_0 (by linarith) h0 hx hv ha

  by_cases h1 : r ≤ ((73/80:ℚ):ℝ)

  · exact cell_1 (by linarith) h1 hx hv ha

  by_cases h2 : r ≤ ((147/160:ℚ):ℝ)

  · exact cell_2 (by linarith) h2 hx hv ha

  by_cases h3 : r ≤ ((37/40:ℚ):ℝ)

  · exact cell_3 (by linarith) h3 hx hv ha

  by_cases h4 : r ≤ ((149/160:ℚ):ℝ)

  · exact cell_4 (by linarith) h4 hx hv ha

  by_cases h5 : r ≤ ((15/16:ℚ):ℝ)

  · exact cell_5 (by linarith) h5 hx hv ha

  by_cases h6 : r ≤ ((151/160:ℚ):ℝ)

  · exact cell_6 (by linarith) h6 hx hv ha

  by_cases h7 : r ≤ ((19/20:ℚ):ℝ)

  · exact cell_7 (by linarith) h7 hx hv ha

  by_cases h8 : r ≤ ((153/160:ℚ):ℝ)

  · exact cell_8 (by linarith) h8 hx hv ha

  by_cases h9 : r ≤ ((77/80:ℚ):ℝ)

  · exact cell_9 (by linarith) h9 hx hv ha

  by_cases h10 : r ≤ ((31/32:ℚ):ℝ)

  · exact cell_10 (by linarith) h10 hx hv ha

  by_cases h11 : r ≤ ((39/40:ℚ):ℝ)

  · exact cell_11 (by linarith) h11 hx hv ha

  by_cases h12 : r ≤ ((157/160:ℚ):ℝ)

  · exact cell_12 (by linarith) h12 hx hv ha

  by_cases h13 : r ≤ ((79/80:ℚ):ℝ)

  · exact cell_13 (by linarith) h13 hx hv ha

  by_cases h14 : r ≤ ((159/160:ℚ):ℝ)

  · exact cell_14 (by linarith) h14 hx hv ha

  by_cases h15 : r ≤ ((1/1:ℚ):ℝ)

  · exact cell_15 (by linarith) h15 hx hv ha

  by_cases h16 : r ≤ ((161/160:ℚ):ℝ)

  · exact cell_16 (by linarith) h16 hx hv ha

  by_cases h17 : r ≤ ((81/80:ℚ):ℝ)

  · exact cell_17 (by linarith) h17 hx hv ha

  by_cases h18 : r ≤ ((163/160:ℚ):ℝ)

  · exact cell_18 (by linarith) h18 hx hv ha

  by_cases h19 : r ≤ ((41/40:ℚ):ℝ)

  · exact cell_19 (by linarith) h19 hx hv ha

  by_cases h20 : r ≤ ((33/32:ℚ):ℝ)

  · exact cell_20 (by linarith) h20 hx hv ha

  by_cases h21 : r ≤ ((83/80:ℚ):ℝ)

  · exact cell_21 (by linarith) h21 hx hv ha

  by_cases h22 : r ≤ ((167/160:ℚ):ℝ)

  · exact cell_22 (by linarith) h22 hx hv ha

  by_cases h23 : r ≤ ((21/20:ℚ):ℝ)

  · exact cell_23 (by linarith) h23 hx hv ha

  by_cases h24 : r ≤ ((169/160:ℚ):ℝ)

  · exact cell_24 (by linarith) h24 hx hv ha

  by_cases h25 : r ≤ ((17/16:ℚ):ℝ)

  · exact cell_25 (by linarith) h25 hx hv ha

  by_cases h26 : r ≤ ((171/160:ℚ):ℝ)

  · exact cell_26 (by linarith) h26 hx hv ha

  by_cases h27 : r ≤ ((43/40:ℚ):ℝ)

  · exact cell_27 (by linarith) h27 hx hv ha

  by_cases h28 : r ≤ ((173/160:ℚ):ℝ)

  · exact cell_28 (by linarith) h28 hx hv ha

  by_cases h29 : r ≤ ((87/80:ℚ):ℝ)

  · exact cell_29 (by linarith) h29 hx hv ha

  by_cases h30 : r ≤ ((35/32:ℚ):ℝ)

  · exact cell_30 (by linarith) h30 hx hv ha

  exact cell_31 (by linarith) (by norm_num; exact hrhi) hx hv ha

#print axioms terminal_energy
end LeanControls.RecoveryTerminal
