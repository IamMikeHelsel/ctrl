module
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Tactic
@[expose] public section
noncomputable section
namespace LeanControls.DirectReference
open Polynomial
open scoped Polynomial

/-- Frozen phase starts, in physical seconds. -/
def phaseStart : ℕ → ℝ
  | 0 => 0
  | 1 => (1/4)
  | 2 => (51/200)
  | 3 => (61/200)
  | 4 => (219/400)
  | 5 => (229/400)
  | 6 => (5235077/7508900)
  | 7 => (10491307/7508900)
  | _ => 3/2

/-- Frozen local durations, in physical seconds. -/
def duration : ℕ → ℝ
  | 0 => (1/4)
  | 1 => (1/200)
  | 2 => (1/20)
  | 3 => (97/400)
  | 4 => (1/40)
  | 5 => (3744927/30035600)
  | 6 => (7/10)
  | 7 => (772043/7508900)
  | _ => 0

/-- The eight exact local-time position polynomials used in the fixed comparison. -/
def position : ℕ → ℝ[X]
  | 0 => C (5/3) * X^3
  | 1 => C (5/192) + C (5/16) * X + C (5/4) * X^2 + C (5/3) * X^3
  | 2 => C (44217/1600000) + C (2601/8000) * X + C (51/40) * X^2 + C (5/3) * X^3 + C (-50/3) * X^4
  | 3 => C (226481/4800000) + C (10963/24000) * X + C (51/40) * X^2 + C (-5/3) * X^3
  | 4 => C (8031973/38400000) + C (74989/96000) * X + C (1/16) * X^2 + C (-5/3) * X^3 + C (50/3) * X^4
  | 5 => C (8782613/38400000) + C (75089/96000) * X
  | 6 => C (626377/1920000) + C (75089/96000) * X + C (-53635/9408) * X^4 + C (53635/5488) * X^5 + C (-268175/57624) * X^6
  | 7 => C (3/5)
  | _ => C (3/5)

end LeanControls.DirectReference
