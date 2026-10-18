import Std
set_option maxRecDepth 2000

/-!
Scalar certificates only, for the partial 2587/100000 bound.
This file does not assert a graph theorem. The paper's external
Balogh--Clemen--Lidicky max-cut theorem is NOT introduced as an axiom.
-/
namespace SparseHalf

def I : Rat := 2 / 47
def T : Rat := 2587 / 100000
def c0 : Rat := 7797 / 10000
def P (c : Rat) : Rat := (T-I-17/32)*c*c+7*c/8+T-3/8
def A : Rat := T+1/4-I
def B : Rat := 3/8
def C : Rat := T+1/8

theorem cap_margin : T-I*c0*c0 = 1291/2350000000 := by decide +kernel
theorem left_margin : P c0 = 312483613/235000000000000 := by decide +kernel
theorem right_margin : P (4/5) = 22649/117500000 := by decide +kernel
theorem discriminant_margin : 4*A*C-B*B = 442569/2500000000 := by decide +kernel
theorem scalar_signs : 0 < A ∧ 0 < 4*A*C-B*B ∧ I*c0*c0 < T ∧
    0 < P c0 ∧ 0 < P (4/5) ∧ T-I-17/32 < 0 := by decide +kernel

theorem square_identity (c : Rat) :
    4*A*(A*c*c-B*c+C) = (2*A*c-B)^2+(4*A*C-B*B) := by
  grind

theorem completion_identity (alpha b : Rat) :
    (1/2-alpha)*(b-alpha)+b*(1/2-b)/2 =
    3/2*alpha^2-5/4*alpha+9/32-(b-(3/4-alpha))^2/2 := by
  grind

theorem average_identity (alpha b r : Rat) :
    (1/2-alpha)*(b-alpha) + (1/2-alpha+b/2)*r -
      (1/2-alpha)*(1-alpha-b)/2 + b*((1/2-b)-r)/2 +
      r*((1/2-b)-r) + ((1/2-b)-r)^2/4 =
    (1/2-alpha)*(b-alpha-(1-alpha-b)/2) + b*(1/2-b)/2 +
      (1/2-b)^2/4 + ((1/2-alpha)+(1/2-b)/2)*r-3*r^2/4 := by
  grind

theorem average_at_cap (alpha b : Rat) :
    (1/2-alpha)*(b-alpha-(1-alpha-b)/2) + b*(1/2-b)/2 +
      (1/2-b)^2/4 + ((1/2-alpha)+(1/2-b)/2)*(1-alpha-b)/2 -
      3*(1-alpha-b)^2/16 =
    alpha*(1/2-alpha)/2 + (1-3*alpha)*(b-alpha)/2-3*(b-alpha)^2/16 := by
  grind

theorem average_derivative_at_cap (alpha b : Rat) :
    (1/2-alpha)+(1/2-b)/2-3*(1-alpha-b)/4 = (b-alpha)/4 := by
  grind

theorem cap_interval (c : Rat) (h0 : 0 ≤ c) (hc : c ≤ c0) :
    I*c*c < T := by
  have hi : 0 ≤ I := by decide +kernel
  have hc0 : 0 ≤ c0 := by decide +kernel
  have hp := Lean.Grind.OrderedRing.mul_nonneg
    (show 0 ≤ c0-c by grind) (show 0 ≤ c0+c by grind)
  have hq := Lean.Grind.OrderedRing.mul_nonneg hi hp
  have heq : I*((c0-c)*(c0+c)) = I*c0*c0-I*c*c := by grind
  have hb : I*c0*c0 < T := scalar_signs.2.2.1
  rw [heq] at hq
  grind -ring only

theorem middle_interval (c : Rat) (hl : c0 ≤ c) (hu : c ≤ 4/5) :
    0 < P c := by
  let a : Rat := T-I-17/32
  have ha : a ≤ 0 := by decide +kernel
  have hm := Lean.Grind.OrderedRing.mul_le_mul_of_nonpos_left
    (show c+c0 ≤ 4/5+c0 by grind) ha
  have hk : 0 < a*(4/5+c0)+7/8 := by decide +kernel
  have hq : 0 ≤ a*(c+c0)+7/8 := by grind
  have hp := Lean.Grind.OrderedRing.mul_nonneg (show 0 ≤ c-c0 by grind) hq
  have heq : P c-P c0 = (c-c0)*(a*(c+c0)+7/8) := by
    unfold P
    dsimp [a]
    grind
  have hb : 0 < P c0 := scalar_signs.2.2.2.1
  rw [← heq] at hp
  grind -ring only

theorem positive_sum (x y : Rat) (hx : 0 ≤ x) (hy : 0 < y) : 0 < x+y := by grind

theorem order_contradiction (x : Rat) (hp : 0 < x) (hn : x ≤ 0) : False := by grind

theorem upper_interval (c : Rat) : 0 < A*c*c-B*c+C := by
  have ha : 0 < A := scalar_signs.1
  have hd : 0 < 4*A*C-B*B := scalar_signs.2.1
  have hs : 0 ≤ (2*A*c-B)^2 := Lean.Grind.OrderedRing.sq_nonneg
  have heq := square_identity c
  by_cases h : 0 < A*c*c-B*c+C
  · exact h
  · have hn : A*c*c-B*c+C ≤ 0 := by grind
    have hm := Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_left hn
      (show 0 ≤ 4*A by grind)
    have hz : 4*A*(A*c*c-B*c+C) ≤ 0 := by simpa using hm
    rw [heq] at hz
    exact False.elim (order_contradiction _ (positive_sum _ _ hs hd) hz)

theorem rational_bound (d beta t r : Rat) (hd : 0 < d)
    (hb : d*beta ≤ r) (hg : 0 < d*t-r) : beta < t := by
  by_cases h : beta < t
  · exact h
  · have hge : t ≤ beta := by grind
    have hm := Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_left hge
      (show 0 ≤ d by grind)
    grind -ring only

/-- Conditional scalar optimization. Its hypotheses must still be supplied
by a formal graph construction before this can certify the graph theorem. -/
theorem scalar_envelope (c beta : Rat) (hc : 0 ≤ c)
    (hcap : beta ≤ I*c*c)
    (hmid : c0 ≤ c → c ≤ 4/5 →
      (1+c*c)*beta ≤ (I+17/32)*c*c-7*c/8+3/8)
    (hu : 4/5 ≤ c →
      (1+c*c)*beta ≤ (I-1/4)*c*c+3*c/8-1/8) : beta < T := by
  have hs : 0 ≤ c^2 := Lean.Grind.OrderedRing.sq_nonneg
  have hd : 0 < 1+c*c := by grind
  by_cases hlow : c ≤ c0
  · have hb := cap_interval c hc hlow
    grind -ring only
  · have hl : c0 ≤ c := by grind
    by_cases hhigh : c ≤ 4/5
    · have heq : (1+c*c)*T-((I+17/32)*c*c-7*c/8+3/8) = P c := by
        unfold P
        grind
      have hg : 0 < (1+c*c)*T-((I+17/32)*c*c-7*c/8+3/8) := by
        rw [heq]
        exact middle_interval c hl hhigh
      exact rational_bound _ _ _ _ hd (hmid hl hhigh) hg
    · have hh : 4/5 ≤ c := by grind
      have heq : (1+c*c)*T-((I-1/4)*c*c+3*c/8-1/8) = A*c*c-B*c+C := by
        unfold A B C
        grind
      have hg : 0 < (1+c*c)*T-((I-1/4)*c*c+3*c/8-1/8) := by
        rw [heq]
        exact upper_interval c
      exact rational_bound _ _ _ _ hd (hu hh) hg

#print axioms cap_margin
#print axioms left_margin
#print axioms right_margin
#print axioms discriminant_margin
#print axioms scalar_signs
#print axioms square_identity
#print axioms completion_identity
#print axioms average_identity
#print axioms average_at_cap
#print axioms average_derivative_at_cap
#print axioms cap_interval
#print axioms middle_interval
#print axioms positive_sum
#print axioms order_contradiction
#print axioms upper_interval
#print axioms rational_bound
#print axioms scalar_envelope
end SparseHalf
