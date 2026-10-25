import Mathlib

/-! # A one-neuron ReLU refutes discrete-time Aizerman *and* Kalman at n = 2

Plant `x⁺ = A x + b u`, `A = [[0,1],[-3/4,-1/2]]`, `b = (0,1)`, output
`y = cᵀx = -x₂`, controller `u = φ(y)`.

* Every linear gain `φ(y) = k y`, `k ∈ [0,1]`, gives a closed loop with the
  exact Lyapunov contraction `V_k(A_k x) = (3/4) V_k(x)`.
* `φ = ReLU` is sector-[0,1] and slope-[0,1], yet the loop has the exact orbit
  `(1,0) ↦ (0,-3/4) ↦ (-3/4,9/8) ↦ (9/8,0)`, so it grows like `(9/8)^{n/3}`.
* Hence no quadratic Lyapunov function is common to the two endpoint gains.

Compare Carrasco–Heath–de la Sen, "Second-order counterexample to the
discrete-time Kalman conjecture", Automatica 60 (2015). -/

noncomputable section
namespace ClassicsFalse

open Filter

def relu (y : ℝ) : ℝ := max y 0

/-- Linear closed loop with gain `k`. -/
def Ak (k : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (x.2, -3/4 * x.1 - 1/2 * x.2 + k * (-x.2))

/-- ReLU closed loop. -/
def F (x : ℝ × ℝ) : ℝ × ℝ := (x.2, -3/4 * x.1 - 1/2 * x.2 + relu (-x.2))

/-- Per-gain Lyapunov function. -/
def V (k : ℝ) (x : ℝ × ℝ) : ℝ := x.2 ^ 2 + (1/2 + k) * x.1 * x.2 + 3/4 * x.1 ^ 2

theorem V_step (k : ℝ) (x : ℝ × ℝ) : V k (Ak k x) = 3/4 * V k x := by
  simp only [V, Ak]; ring

theorem sq_le_V {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (x : ℝ × ℝ) :
    x.1 ^ 2 + x.2 ^ 2 ≤ 16 * V k x := by
  simp only [V]
  have ht : (1/2 + k) ^ 2 ≤ 9/4 := by nlinarith
  nlinarith [sq_nonneg (x.2 + (1/2 + k)/2 * x.1), sq_nonneg x.1,
    sq_nonneg (x.2 - (1/2 + k)/2 * x.1), mul_nonneg (sq_nonneg x.1) (by linarith : 0 ≤ 9/4 - (1/2+k)^2)]

/-- **Every linear gain in the sector is (exponentially) stable.** -/
theorem linear_stable {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (x : ℝ × ℝ) :
    Tendsto (fun n => ((Ak k)^[n] x).1 ^ 2 + ((Ak k)^[n] x).2 ^ 2) atTop (nhds 0) := by
  have hV : ∀ n, V k ((Ak k)^[n] x) = (3/4) ^ n * V k x := by
    intro n; induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', V_step, ih]; ring
  have hlim : Tendsto (fun n : ℕ => 16 * ((3/4 : ℝ) ^ n * V k x)) atTop (nhds 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 3/4)
      (by norm_num)).mul_const (V k x)
    simpa using this.const_mul 16
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
  · intro n; positivity
  · intro n; have := sq_le_V hk0 hk1 ((Ak k)^[n] x); rw [hV] at this; exact this

/-- The whole Schur sector actually extends beyond `[0,1]`; we only need `[0,1]`. -/
theorem relu_sector (y : ℝ) : 0 ≤ relu y * y ∧ relu y * y ≤ 1 * y ^ 2 := by
  unfold relu; rcases le_total y 0 with h | h
  · rw [max_eq_right h]; constructor <;> nlinarith
  · rw [max_eq_left h]; constructor <;> nlinarith

theorem relu_slope (x y : ℝ) :
    0 ≤ (relu x - relu y) * (x - y) ∧ (relu x - relu y) * (x - y) ≤ 1 * (x - y) ^ 2 := by
  unfold relu
  rcases le_total x 0 with hx | hx <;> rcases le_total y 0 with hy | hy <;>
    simp only [max_eq_right, max_eq_left, hx, hy] <;> constructor <;> nlinarith

/-- The ReLU loop is pointwise one of the two endpoint linear loops. -/
theorem F_eq (x : ℝ × ℝ) : F x = if 0 ≤ x.2 then Ak 0 x else Ak 1 x := by
  unfold F Ak relu
  split_ifs with h
  · rw [max_eq_right (by linarith)]; simp
  · rw [max_eq_left (by linarith)]; ext <;> simp

theorem F3 {s : ℝ} (hs : 0 ≤ s) : F (F (F (s, 0))) = (9/8 * s, 0) := by
  have h1 : F (s, 0) = (0, -3/4 * s) := by
    simp only [F, relu, neg_zero, max_self]; ext <;> simp
  have h2 : F (0, -3/4 * s) = (-3/4 * s, 9/8 * s) := by
    simp only [F, relu]; rw [max_eq_left (by linarith)]; ext <;> simp; ring
  have h3 : F (-3/4 * s, 9/8 * s) = (9/8 * s, 0) := by
    simp only [F, relu]; rw [max_eq_right (by linarith)]; ext <;> simp; ring
  rw [h1, h2, h3]

theorem orbit (n : ℕ) : F^[3 * n] (1, 0) = ((9/8 : ℝ) ^ n, 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 3 * (n + 1) = 3 + 3 * n by ring, Function.iterate_add_apply, ih]
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    rw [F3 (by positivity)]; ring_nf

/-- **The ReLU loop is unbounded.** -/
theorem relu_loop_unbounded : ¬ BddAbove (Set.range fun n => (F^[n] (1, 0)).1) := by
  rintro ⟨M, hM⟩
  obtain ⟨n, hn⟩ := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 9/8)).eventually_gt_atTop M
    |>.exists
  have := hM ⟨3 * n, rfl⟩
  simp only [orbit] at this
  linarith

/-- **Discrete-time Aizerman/Kalman fail at n = 2, with a single ReLU.** -/
theorem discrete_aizerman_kalman_false :
    (∀ k ∈ Set.Icc (0:ℝ) 1, ∀ x : ℝ × ℝ,
      Tendsto (fun n => ((Ak k)^[n] x).1 ^ 2 + ((Ak k)^[n] x).2 ^ 2) atTop (nhds 0)) ∧
    (∀ x y, 0 ≤ (relu x - relu y) * (x - y) ∧ (relu x - relu y) * (x - y) ≤ 1 * (x - y) ^ 2) ∧
    ¬ BddAbove (Set.range fun n => (F^[n] (1, 0)).1) :=
  ⟨fun _ hk x => linear_stable hk.1 hk.2 x, relu_slope, relu_loop_unbounded⟩

/-- **No common quadratic Lyapunov function** for the endpoint gains `k = 0, 1`
(so the circle/Popov-type "common certificate" route must fail here). -/
theorem no_common_quadratic_lyapunov (p q r : ℝ) (hp : 0 < p) :
    ¬ (∀ x : ℝ × ℝ, (let W := fun z : ℝ × ℝ => p * z.1 ^ 2 + q * z.1 * z.2 + r * z.2 ^ 2
        W (Ak 0 x) ≤ W x ∧ W (Ak 1 x) ≤ W x)) := by
  intro h
  set W := fun z : ℝ × ℝ => p * z.1 ^ 2 + q * z.1 * z.2 + r * z.2 ^ 2 with hW
  have hF : ∀ x, W (F x) ≤ W x := by
    intro x; rw [F_eq]; split_ifs
    · exact (h x).1
    · exact (h x).2
  have := (hF _).trans ((hF _).trans (hF (1, 0)))
  rw [F3 zero_le_one] at this
  simp only [hW] at this
  nlinarith

end ClassicsFalse
end

#print axioms ClassicsFalse.discrete_aizerman_kalman_false
#print axioms ClassicsFalse.no_common_quadratic_lyapunov
