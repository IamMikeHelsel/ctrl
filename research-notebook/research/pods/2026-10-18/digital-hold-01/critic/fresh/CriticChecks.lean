import DispatchWitness
open Set
open LeanControls.DigitalHold
namespace IndependentCritic
example : (103621708/1000000000:ℝ) + 98304/1000000*radius = 136350047/1250000000 := by
  norm_num [radius]
example : (2*radius - ((103621708/1000000000:ℝ) + 98304/1000000*radius)) = 2462453/1250000000 := by
  norm_num [radius]
example {H c t : ℝ} {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State}
    (ex : Execution H c f r d stamp read) (b : Bool) (ht : t ∈ Icc 0 H) : ¬ t < stamp b t := by
  exact not_lt_of_ge (ex.causal b t ht).2.1
example {H : ℝ} (hH : 0 ≤ H) {q : Schedule} {stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State}
    (hs : IsSchedule H q stamp read) (b : Bool) : stamp b 0=0 := by
  exact (first_command_fresh hH hs b).1
example : (0:ℝ)-1 ≤ 1/1000 ∧ ¬ (1:ℝ) ≤ 0 := by norm_num
example : ¬ ((103621708/1000000000:ℝ) + 98304/1000000*radius ≤ 2*radius-1/500) := by
  norm_num [radius]
example : |command 0 (![-1/1000,-1/100,-1/20]) - command 0 (![0,0,0])| = 93/1000 := by
  norm_num [command]
example : |command 0 (![-1/1000,-1/100,-1/20]) - command 0 (![0,0,0])| > 92/1000 := by
  norm_num [command]
example : ¬ DifferentiableAt ℝ (fun t => DispatchWitness.state t 2) DispatchWitness.switch :=
  DispatchWitness.not_classical_at_dispatch
example : ∀ t ∈ Icc 0 (1/1000:ℝ), ∀ i,
    |coordinates 0 (DispatchWitness.state t) i| ≤ radius := by
  exact (sampled_hold (by norm_num) DispatchWitness.two_cell_sampled_execution.1
    DispatchWitness.two_cell_sampled_execution.2).2.1
end IndependentCritic
