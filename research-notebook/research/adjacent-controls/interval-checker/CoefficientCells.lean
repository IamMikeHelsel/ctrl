module
public import CoefficientBounds
@[expose] public section
noncomputable section
namespace LeanControls.CoefficientCells
open CoefficientBounds
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem expPoly_expanded (r : ℝ) : expPoly r = ((1/1:ℚ):ℝ)*r^0 + ((-1/20:ℚ):ℝ)*r^1 + ((1/800:ℚ):ℝ)*r^2 + ((-1/48000:ℚ):ℝ)*r^3 + ((1/3840000:ℚ):ℝ)*r^4 + ((-1/384000000:ℚ):ℝ)*r^5 + ((1/46080000000:ℚ):ℝ)*r^6 + ((-1/6451200000000:ℚ):ℝ)*r^7 + ((1/1032192000000000:ℚ):ℝ)*r^8 + ((-1/185794560000000000:ℚ):ℝ)*r^9 := by
  norm_num [expPoly, Finset.sum_range_succ, Nat.factorial]
  ring

theorem velocityPoly_expanded (r : ℝ) : velocityPoly r = ((1/20:ℚ):ℝ)*r^0 + ((-1/800:ℚ):ℝ)*r^1 + ((1/48000:ℚ):ℝ)*r^2 + ((-1/3840000:ℚ):ℝ)*r^3 + ((1/384000000:ℚ):ℝ)*r^4 + ((-1/46080000000:ℚ):ℝ)*r^5 + ((1/6451200000000:ℚ):ℝ)*r^6 + ((-1/1032192000000000:ℚ):ℝ)*r^7 + ((1/185794560000000000:ℚ):ℝ)*r^8 := by
  norm_num [velocityPoly, Finset.sum_range_succ, Nat.factorial]
  ring

theorem positionPoly_expanded (r : ℝ) : positionPoly r = ((1/800:ℚ):ℝ)*r^0 + ((-1/48000:ℚ):ℝ)*r^1 + ((1/3840000:ℚ):ℝ)*r^2 + ((-1/384000000:ℚ):ℝ)*r^3 + ((1/46080000000:ℚ):ℝ)*r^4 + ((-1/6451200000000:ℚ):ℝ)*r^5 + ((1/1032192000000000:ℚ):ℝ)*r^6 + ((-1/185794560000000000:ℚ):ℝ)*r^7 := by
  norm_num [positionPoly, Finset.sum_range_succ, Nat.factorial]
  ring

theorem cell_0 {r : ℝ} (hrlo : ((9/10:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((73/80:ℚ):ℝ)) :
    (((11942148001/12500000000:ℚ):ℝ) ≤ Real.exp (-r/20) ∧ Real.exp (-r/20) ≤ ((1493790331/1562500000:ℚ):ℝ)) ∧ (((48876053829/1000000000000:ℚ):ℝ) ≤ (1-Real.exp (-r/20))/r ∧ (1-Real.exp (-r/20))/r ≤ ((12223039739/250000000000:ℚ):ℝ)) ∧ (((246239711/200000000000:ℚ):ℝ) ≤ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ∧ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ≤ ((307866239/250000000000:ℚ):ℝ)) := by
  obtain ⟨δ, hd, he, hb, hc⟩ := shared_remainder (r := r) (by linarith) (by linarith)
  have hdlo := (abs_le.mp hd).1
  have hdhi := (abs_le.mp hd).2
  have hirlo : ((80/73:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((10/9:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((9/10:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  have hb' : (1-Real.exp (-r/20))/r = velocityPoly r - δ*r⁻¹ :=
    hb.trans (by rw [div_eq_mul_inv])
  have hc' : (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 = positionPoly r + δ*(r⁻¹)^2 :=
    hc.trans (by rw [div_eq_mul_inv, ← inv_pow])
  rw [hc', hb', he, expPoly_expanded, velocityPoly_expanded, positionPoly_expanded]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    dyadic_interval (native := false) [prec := 60]

theorem cell_1 {r : ℝ} (hrlo : ((73/80:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((37/40:ℚ):ℝ)) :
    (((119346813813/125000000000:ℚ):ℝ) ≤ Real.exp (-r/20) ∧ Real.exp (-r/20) ≤ ((7643431129/8000000000:ℚ):ℝ)) ∧ (((48860892687/1000000000000:ℚ):ℝ) ≤ (1-Real.exp (-r/20))/r ∧ (1-Real.exp (-r/20))/r ≤ ((48877004551/1000000000000:ℚ):ℝ)) ∧ (((1230943957/1000000000000:ℚ):ℝ) ≤ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ∧ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ≤ ((1231210441/1000000000000:ℚ):ℝ)) := by
  obtain ⟨δ, hd, he, hb, hc⟩ := shared_remainder (r := r) (by linarith) (by linarith)
  have hdlo := (abs_le.mp hd).1
  have hdhi := (abs_le.mp hd).2
  have hirlo : ((40/37:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((80/73:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((73/80:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  have hb' : (1-Real.exp (-r/20))/r = velocityPoly r - δ*r⁻¹ :=
    hb.trans (by rw [div_eq_mul_inv])
  have hc' : (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 = positionPoly r + δ*(r⁻¹)^2 :=
    hc.trans (by rw [div_eq_mul_inv, ← inv_pow])
  rw [hc', hb', he, expPoly_expanded, velocityPoly_expanded, positionPoly_expanded]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    dyadic_interval (native := false) [prec := 60]

theorem cell_2 {r : ℝ} (hrlo : ((37/40:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((15/16:ℚ):ℝ)) :
    (((29818048559/31250000000:ℚ):ℝ) ≤ Real.exp (-r/20) ∧ Real.exp (-r/20) ≤ ((119354042953/125000000000:ℚ):ℝ)) ∧ (((48845737833/1000000000000:ℚ):ℝ) ≤ (1-Real.exp (-r/20))/r ∧ (1-Real.exp (-r/20))/r ≤ ((24430928219/500000000000:ℚ):ℝ)) ∧ (((615344719/500000000000:ℚ):ℝ) ≤ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ∧ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ≤ ((615478003/500000000000:ℚ):ℝ)) := by
  obtain ⟨δ, hd, he, hb, hc⟩ := shared_remainder (r := r) (by linarith) (by linarith)
  have hdlo := (abs_le.mp hd).1
  have hdhi := (abs_le.mp hd).2
  have hirlo : ((16/15:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((40/37:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((37/40:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  have hb' : (1-Real.exp (-r/20))/r = velocityPoly r - δ*r⁻¹ :=
    hb.trans (by rw [div_eq_mul_inv])
  have hc' : (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 = positionPoly r + δ*(r⁻¹)^2 :=
    hc.trans (by rw [div_eq_mul_inv, ← inv_pow])
  rw [hc', hb', he, expPoly_expanded, velocityPoly_expanded, positionPoly_expanded]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    dyadic_interval (native := false) [prec := 60]

theorem cell_3 {r : ℝ} (hrlo : ((15/16:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((19/20:ℚ):ℝ)) :
    (((953580969997/1000000000000:ℚ):ℝ) ≤ Real.exp (-r/20) ∧ Real.exp (-r/20) ≤ ((190847233821/200000000000:ℚ):ℝ)) ∧ (((24415294633/500000000000:ℚ):ℝ) ≤ (1-Real.exp (-r/20))/r ∧ (1-Real.exp (-r/20))/r ≤ ((24423357307/500000000000:ℚ):ℝ)) ∧ (((615217499/500000000000:ℚ):ℝ) ≤ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ∧ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ≤ ((1230701649/1000000000000:ℚ):ℝ)) := by
  obtain ⟨δ, hd, he, hb, hc⟩ := shared_remainder (r := r) (by linarith) (by linarith)
  have hdlo := (abs_le.mp hd).1
  have hdhi := (abs_le.mp hd).2
  have hirlo : ((20/19:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((16/15:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((15/16:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  have hb' : (1-Real.exp (-r/20))/r = velocityPoly r - δ*r⁻¹ :=
    hb.trans (by rw [div_eq_mul_inv])
  have hc' : (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 = positionPoly r + δ*(r⁻¹)^2 :=
    hc.trans (by rw [div_eq_mul_inv, ← inv_pow])
  rw [hc', hb', he, expPoly_expanded, velocityPoly_expanded, positionPoly_expanded]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    dyadic_interval (native := false) [prec := 60]

theorem cell_4 {r : ℝ} (hrlo : ((19/20:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((77/80:ℚ):ℝ)) :
    (((952984758599/1000000000000:ℚ):ℝ) ≤ Real.exp (-r/20) ∧ Real.exp (-r/20) ≤ ((476820183667/500000000000:ℚ):ℝ)) ∧ (((2440772349/50000000000:ℚ):ℝ) ≤ (1-Real.exp (-r/20))/r ∧ (1-Real.exp (-r/20))/r ≤ ((1953263163/40000000000:ℚ):ℝ)) ∧ (((1230180637/1000000000000:ℚ):ℝ) ≤ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ∧ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ≤ ((307611843/250000000000:ℚ):ℝ)) := by
  obtain ⟨δ, hd, he, hb, hc⟩ := shared_remainder (r := r) (by linarith) (by linarith)
  have hdlo := (abs_le.mp hd).1
  have hdhi := (abs_le.mp hd).2
  have hirlo : ((80/77:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((20/19:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((19/20:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  have hb' : (1-Real.exp (-r/20))/r = velocityPoly r - δ*r⁻¹ :=
    hb.trans (by rw [div_eq_mul_inv])
  have hc' : (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 = positionPoly r + δ*(r⁻¹)^2 :=
    hc.trans (by rw [div_eq_mul_inv, ← inv_pow])
  rw [hc', hb', he, expPoly_expanded, velocityPoly_expanded, positionPoly_expanded]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    dyadic_interval (native := false) [prec := 60]

theorem cell_5 {r : ℝ} (hrlo : ((77/80:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((39/40:ℚ):ℝ)) :
    (((47619445973/50000000000:ℚ):ℝ) ≤ Real.exp (-r/20) ∧ Real.exp (-r/20) ≤ ((953044938079/1000000000000:ℚ):ℝ)) ∧ (((1952012439/40000000000:ℚ):ℝ) ≤ (1-Real.exp (-r/20))/r ∧ (1-Real.exp (-r/20))/r ≤ ((2440822491/50000000000:ℚ):ℝ)) ∧ (((245985271/200000000000:ℚ):ℝ) ≤ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ∧ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ≤ ((615096587/500000000000:ℚ):ℝ)) := by
  obtain ⟨δ, hd, he, hb, hc⟩ := shared_remainder (r := r) (by linarith) (by linarith)
  have hdlo := (abs_le.mp hd).1
  have hdhi := (abs_le.mp hd).2
  have hirlo : ((40/39:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((80/77:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((77/80:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  have hb' : (1-Real.exp (-r/20))/r = velocityPoly r - δ*r⁻¹ :=
    hb.trans (by rw [div_eq_mul_inv])
  have hc' : (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 = positionPoly r + δ*(r⁻¹)^2 :=
    hc.trans (by rw [div_eq_mul_inv, ← inv_pow])
  rw [hc', hb', he, expPoly_expanded, velocityPoly_expanded, positionPoly_expanded]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    dyadic_interval (native := false) [prec := 60]

theorem cell_6 {r : ℝ} (hrlo : ((39/40:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((79/80:ℚ):ℝ)) :
    (((951793452349/1000000000000:ℚ):ℝ) ≤ Real.exp (-r/20) ∧ Real.exp (-r/20) ≤ ((952449881107/1000000000000:ℚ):ℝ)) ∧ (((48785181247/1000000000000:ℚ):ℝ) ≤ (1-Real.exp (-r/20))/r ∧ (1-Real.exp (-r/20))/r ≤ ((12200331711/250000000000:ℚ):ℝ)) ∧ (((153709019/125000000000:ℚ):ℝ) ≤ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ∧ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ≤ ((245987811/200000000000:ℚ):ℝ)) := by
  obtain ⟨δ, hd, he, hb, hc⟩ := shared_remainder (r := r) (by linarith) (by linarith)
  have hdlo := (abs_le.mp hd).1
  have hdhi := (abs_le.mp hd).2
  have hirlo : ((80/79:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((40/39:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((39/40:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  have hb' : (1-Real.exp (-r/20))/r = velocityPoly r - δ*r⁻¹ :=
    hb.trans (by rw [div_eq_mul_inv])
  have hc' : (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 = positionPoly r + δ*(r⁻¹)^2 :=
    hc.trans (by rw [div_eq_mul_inv, ← inv_pow])
  rw [hc', hb', he, expPoly_expanded, velocityPoly_expanded, positionPoly_expanded]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    dyadic_interval (native := false) [prec := 60]

theorem cell_7 {r : ℝ} (hrlo : ((79/80:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((1/1:ℚ):ℝ)) :
    (((951198357031/1000000000000:ℚ):ℝ) ≤ Real.exp (-r/20) ∧ Real.exp (-r/20) ≤ ((475927598093/500000000000:ℚ):ℝ)) ∧ (((762032153/15625000000:ℚ):ℝ) ≤ (1-Real.exp (-r/20))/r ∧ (1-Real.exp (-r/20))/r ≤ ((24393105073/500000000000:ℚ):ℝ)) ∧ (((307354507/250000000000:ℚ):ℝ) ≤ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ∧ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ≤ ((245937003/200000000000:ℚ):ℝ)) := by
  obtain ⟨δ, hd, he, hb, hc⟩ := shared_remainder (r := r) (by linarith) (by linarith)
  have hdlo := (abs_le.mp hd).1
  have hdhi := (abs_le.mp hd).2
  have hirlo : ((1/1:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((80/79:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((79/80:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  have hb' : (1-Real.exp (-r/20))/r = velocityPoly r - δ*r⁻¹ :=
    hb.trans (by rw [div_eq_mul_inv])
  have hc' : (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 = positionPoly r + δ*(r⁻¹)^2 :=
    hc.trans (by rw [div_eq_mul_inv, ← inv_pow])
  rw [hc', hb', he, expPoly_expanded, velocityPoly_expanded, positionPoly_expanded]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    dyadic_interval (native := false) [prec := 60]

theorem cell_8 {r : ℝ} (hrlo : ((1/1:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((81/80:ℚ):ℝ)) :
    (((237650908319/250000000000:ℚ):ℝ) ≤ Real.exp (-r/20) ∧ Real.exp (-r/20) ≤ ((951260883083/1000000000000:ℚ):ℝ)) ∧ (((761795947/15625000000:ℚ):ℝ) ≤ (1-Real.exp (-r/20))/r ∧ (1-Real.exp (-r/20))/r ≤ ((24385549861/500000000000:ℚ):ℝ)) ∧ (((76822749/62500000000:ℚ):ℝ) ≤ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ∧ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ≤ ((614715527/500000000000:ℚ):ℝ)) := by
  obtain ⟨δ, hd, he, hb, hc⟩ := shared_remainder (r := r) (by linarith) (by linarith)
  have hdlo := (abs_le.mp hd).1
  have hdhi := (abs_le.mp hd).2
  have hirlo : ((80/81:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((1/1:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((1/1:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  have hb' : (1-Real.exp (-r/20))/r = velocityPoly r - δ*r⁻¹ :=
    hb.trans (by rw [div_eq_mul_inv])
  have hc' : (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 = positionPoly r + δ*(r⁻¹)^2 :=
    hc.trans (by rw [div_eq_mul_inv, ← inv_pow])
  rw [hc', hb', he, expPoly_expanded, velocityPoly_expanded, positionPoly_expanded]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    dyadic_interval (native := false) [prec := 60]

theorem cell_9 {r : ℝ} (hrlo : ((81/80:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((41/40:ℚ):ℝ)) :
    (((19000185617/20000000000:ℚ):ℝ) ≤ Real.exp (-r/20) ∧ Real.exp (-r/20) ≤ ((950666941567/1000000000000:ℚ):ℝ)) ∧ (((48739829693/1000000000000:ℚ):ℝ) ≤ (1-Real.exp (-r/20))/r ∧ (1-Real.exp (-r/20))/r ≤ ((48755995569/1000000000000:ℚ):ℝ)) ∧ (((614455009/500000000000:ℚ):ℝ) ≤ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ∧ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ≤ ((1229177173/1000000000000:ℚ):ℝ)) := by
  obtain ⟨δ, hd, he, hb, hc⟩ := shared_remainder (r := r) (by linarith) (by linarith)
  have hdlo := (abs_le.mp hd).1
  have hdhi := (abs_le.mp hd).2
  have hirlo : ((40/41:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((80/81:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((81/80:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  have hb' : (1-Real.exp (-r/20))/r = velocityPoly r - δ*r⁻¹ :=
    hb.trans (by rw [div_eq_mul_inv])
  have hc' : (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 = positionPoly r + δ*(r⁻¹)^2 :=
    hc.trans (by rw [div_eq_mul_inv, ← inv_pow])
  rw [hc', hb', he, expPoly_expanded, velocityPoly_expanded, positionPoly_expanded]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    dyadic_interval (native := false) [prec := 60]

theorem cell_10 {r : ℝ} (hrlo : ((41/40:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((83/80:ℚ):ℝ)) :
    (((474707649761/500000000000:ℚ):ℝ) ≤ Real.exp (-r/20) ∧ Real.exp (-r/20) ≤ ((190014674281/200000000000:ℚ):ℝ)) ∧ (((24362362521/500000000000:ℚ):ℝ) ≤ (1-Real.exp (-r/20))/r ∧ (1-Real.exp (-r/20))/r ≤ ((12185224421/250000000000:ℚ):ℝ)) ∧ (((1228656131/1000000000000:ℚ):ℝ) ≤ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ∧ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ≤ ((122892337/100000000000:ℚ):ℝ)) := by
  obtain ⟨δ, hd, he, hb, hc⟩ := shared_remainder (r := r) (by linarith) (by linarith)
  have hdlo := (abs_le.mp hd).1
  have hdhi := (abs_le.mp hd).2
  have hirlo : ((80/83:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((40/41:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((41/40:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  have hb' : (1-Real.exp (-r/20))/r = velocityPoly r - δ*r⁻¹ :=
    hb.trans (by rw [div_eq_mul_inv])
  have hc' : (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 = positionPoly r + δ*(r⁻¹)^2 :=
    hc.trans (by rw [div_eq_mul_inv, ← inv_pow])
  rw [hc', hb', he, expPoly_expanded, velocityPoly_expanded, positionPoly_expanded]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    dyadic_interval (native := false) [prec := 60]

theorem cell_11 {r : ℝ} (hrlo : ((83/80:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((21/20:ℚ):ℝ)) :
    (((948821689059/1000000000000:ℚ):ℝ) ≤ Real.exp (-r/20) ∧ Real.exp (-r/20) ≤ ((189896034473/200000000000:ℚ):ℝ)) ∧ (((24354813327/500000000000:ℚ):ℝ) ≤ (1-Real.exp (-r/20))/r ∧ (1-Real.exp (-r/20))/r ≤ ((9745161213/200000000000:ℚ):ℝ)) ∧ (((1228402323/1000000000000:ℚ):ℝ) ≤ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ∧ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ≤ ((245733929/200000000000:ℚ):ℝ)) := by
  obtain ⟨δ, hd, he, hb, hc⟩ := shared_remainder (r := r) (by linarith) (by linarith)
  have hdlo := (abs_le.mp hd).1
  have hdhi := (abs_le.mp hd).2
  have hirlo : ((20/21:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((80/83:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((83/80:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  have hb' : (1-Real.exp (-r/20))/r = velocityPoly r - δ*r⁻¹ :=
    hb.trans (by rw [div_eq_mul_inv])
  have hc' : (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 = positionPoly r + δ*(r⁻¹)^2 :=
    hc.trans (by rw [div_eq_mul_inv, ← inv_pow])
  rw [hc', hb', he, expPoly_expanded, velocityPoly_expanded, positionPoly_expanded]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    dyadic_interval (native := false) [prec := 60]

theorem cell_12 {r : ℝ} (hrlo : ((21/20:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((17/16:ℚ):ℝ)) :
    (((948228449229/1000000000000:ℚ):ℝ) ≤ Real.exp (-r/20) ∧ Real.exp (-r/20) ≤ ((118610918027/125000000000:ℚ):ℝ)) ∧ (((1947781381/40000000000:ℚ):ℝ) ≤ (1-Real.exp (-r/20))/r ∧ (1-Real.exp (-r/20))/r ≤ ((12177680177/250000000000:ℚ):ℝ)) ∧ (((614074297/500000000000:ℚ):ℝ) ≤ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ∧ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ≤ ((9597/7812500:ℚ):ℝ)) := by
  obtain ⟨δ, hd, he, hb, hc⟩ := shared_remainder (r := r) (by linarith) (by linarith)
  have hdlo := (abs_le.mp hd).1
  have hdhi := (abs_le.mp hd).2
  have hirlo : ((16/17:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((20/21:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((21/20:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  have hb' : (1-Real.exp (-r/20))/r = velocityPoly r - δ*r⁻¹ :=
    hb.trans (by rw [div_eq_mul_inv])
  have hc' : (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 = positionPoly r + δ*(r⁻¹)^2 :=
    hc.trans (by rw [div_eq_mul_inv, ← inv_pow])
  rw [hc', hb', he, expPoly_expanded, velocityPoly_expanded, positionPoly_expanded]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    dyadic_interval (native := false) [prec := 60]

theorem cell_13 {r : ℝ} (hrlo : ((17/16:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((43/40:ℚ):ℝ)) :
    (((947635579801/1000000000000:ℚ):ℝ) ≤ Real.exp (-r/20) ∧ Real.exp (-r/20) ≤ ((948294886727/1000000000000:ℚ):ℝ)) ∧ (((12169862163/250000000000:ℚ):ℝ) ≤ (1-Real.exp (-r/20))/r ∧ (1-Real.exp (-r/20))/r ≤ ((48695641611/1000000000000:ℚ):ℝ)) ∧ (((1227894943/1000000000000:ℚ):ℝ) ≤ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ∧ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ≤ ((614081217/500000000000:ℚ):ℝ)) := by
  obtain ⟨δ, hd, he, hb, hc⟩ := shared_remainder (r := r) (by linarith) (by linarith)
  have hdlo := (abs_le.mp hd).1
  have hdhi := (abs_le.mp hd).2
  have hirlo : ((40/43:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((16/17:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((17/16:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  have hb' : (1-Real.exp (-r/20))/r = velocityPoly r - δ*r⁻¹ :=
    hb.trans (by rw [div_eq_mul_inv])
  have hc' : (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 = positionPoly r + δ*(r⁻¹)^2 :=
    hc.trans (by rw [div_eq_mul_inv, ← inv_pow])
  rw [hc', hb', he, expPoly_expanded, velocityPoly_expanded, positionPoly_expanded]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    dyadic_interval (native := false) [prec := 60]

theorem cell_14 {r : ℝ} (hrlo : ((43/40:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((87/80:ℚ):ℝ)) :
    (((947043080543/1000000000000:ℚ):ℝ) ≤ Real.exp (-r/20) ∧ Real.exp (-r/20) ≤ ((189540559933/200000000000:ℚ):ℝ)) ∧ (((6083046129/125000000000:ℚ):ℝ) ≤ (1-Real.exp (-r/20))/r ∧ (1-Real.exp (-r/20))/r ≤ ((4868056877/100000000000:ℚ):ℝ)) ∧ (((306910343/250000000000:ℚ):ℝ) ≤ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ∧ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ≤ ((1227908947/1000000000000:ℚ):ℝ)) := by
  obtain ⟨δ, hd, he, hb, hc⟩ := shared_remainder (r := r) (by linarith) (by linarith)
  have hdlo := (abs_le.mp hd).1
  have hdhi := (abs_le.mp hd).2
  have hirlo : ((80/87:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((40/43:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((43/40:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  have hb' : (1-Real.exp (-r/20))/r = velocityPoly r - δ*r⁻¹ :=
    hb.trans (by rw [div_eq_mul_inv])
  have hc' : (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 = positionPoly r + δ*(r⁻¹)^2 :=
    hc.trans (by rw [div_eq_mul_inv, ← inv_pow])
  rw [hc', hb', he, expPoly_expanded, velocityPoly_expanded, positionPoly_expanded]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    dyadic_interval (native := false) [prec := 60]

theorem cell_15 {r : ℝ} (hrlo : ((87/80:ℚ):ℝ) ≤ r) (hrhi : r ≤ ((11/10:ℚ):ℝ)) :
    (((118306368903/125000000000:ℚ):ℝ) ≤ Real.exp (-r/20) ∧ Real.exp (-r/20) ≤ ((947111082799/1000000000000:ℚ):ℝ)) ∧ (((48649295663/1000000000000:ℚ):ℝ) ≤ (1-Real.exp (-r/20))/r ∧ (1-Real.exp (-r/20))/r ≤ ((48665502183/1000000000000:ℚ):ℝ)) ∧ (((1227387879/1000000000000:ℚ):ℝ) ≤ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ∧ (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 ≤ ((613827769/500000000000:ℚ):ℝ)) := by
  obtain ⟨δ, hd, he, hb, hc⟩ := shared_remainder (r := r) (by linarith) (by linarith)
  have hdlo := (abs_le.mp hd).1
  have hdhi := (abs_le.mp hd).2
  have hirlo : ((10/11:ℚ):ℝ) ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ ((80/87:ℚ):ℝ) := by
    have hh := one_div_le_one_div_of_le (show 0 < ((87/80:ℚ):ℝ) by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  have hb' : (1-Real.exp (-r/20))/r = velocityPoly r - δ*r⁻¹ :=
    hb.trans (by rw [div_eq_mul_inv])
  have hc' : (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 = positionPoly r + δ*(r⁻¹)^2 :=
    hc.trans (by rw [div_eq_mul_inv, ← inv_pow])
  rw [hc', hb', he, expPoly_expanded, velocityPoly_expanded, positionPoly_expanded]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    dyadic_interval (native := false) [prec := 60]

end LeanControls.CoefficientCells
