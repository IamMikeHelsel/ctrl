import domain_assembly

noncomputable section
set_option autoImplicit false
namespace S01SourceBridge
open Set Filter LeanControls LeanControls.DigitalHold LeanControls.ConstructiveHold
open LeanControls.ConstructedHandoff LeanControls.DetectorBridge LeanControls.DetectorSampling

variable {f : ℝ → State} {rL qL rB qB : ℝ → ℝ} {m : ℕ → State}
variable (ex : BrakingExecution f rL qL rB qB) (hm : Readings f m)
variable {k : ℕ} (hk : k ≤ 1058) (hf : First m k)
variable {R δ : ℕ → ℝ} {ε : ℕ → State}
variable (hr : ∀ n, 1 ≤ n → 8 ≤ R n ∧ R n ≤ 12)
variable (hd : ∀ n, 1 ≤ n → |δ n| ≤ 1/100)
variable (he : ∀ n, |ε n 0| ≤ 1/1000 ∧ |ε n 1| ≤ 1/100 ∧ |ε n 2| ≤ 1/20)
include ex hm hk hf hr hd he

/-- Original phase-open loss ODE, with no new claim at the switching instant. -/
theorem global_loss_ode {t : ℝ} (ht : t ∈ Ioo (0:ℝ) (1/20)) (i : Fin 3) :
    HasDerivAt (fun s => globalTrajectory f m k R δ ε s i)
      (![f t 1,f t 2,rL t*(qL t-f t 2)] i) t := by
  have a := assemble ex hm hk hf (by norm_num : 2≤2) hr hd he
  have hlarge : t < grid k+grid 2 := by
    have hb := grid_strict.monotone a.bounds.1
    norm_num [grid] at hb ⊢
    linarith [ht.2]
  apply (a.loss_ode t ht i).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hlarge] with s hs
  exact congrArg (fun z => z i)
    (global_trajectory_prefix f m k 2 R δ ε (by norm_num) hs.le)

/-- Original phase-open brake ODE, including the pending interval. -/
theorem global_brake_ode {t : ℝ} (ht : t ∈ Ioo (1/20:ℝ) (grid k+h)) (i : Fin 3) :
    HasDerivAt (fun s => globalTrajectory f m k R δ ε s i)
      (![f t 1,f t 2,rB (t-1/20)*(qB (t-1/20)-f t 2)] i) t := by
  have a := assemble ex hm hk hf (by norm_num : 2≤2) hr hd he
  have hlarge : t < grid k+grid 2 := by
    have hh : h < grid 2 := by norm_num [h,grid]
    linarith [ht.2]
  apply (a.brake_ode t ht i).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hlarge] with s hs
  exact congrArg (fun z => z i)
    (global_trajectory_prefix f m k 2 R δ ε (by norm_num) hs.le)

#print axioms global_loss_ode
#print axioms global_brake_ode
end S01SourceBridge
