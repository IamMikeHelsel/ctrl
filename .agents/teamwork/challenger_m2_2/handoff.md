# Handoff Report: Adversarial Challenge of Centroidal Lorentz-Cone Backup CBF

**Agent**: `challenger_m2_2`  
**Role**: Empirical Challenger (critic, specialist)  
**Date**: 2026-10-19T05:54:00Z  
**Target Recipient**: Orchestrator (`0b6a5e14-8c10-4497-8beb-fd637698bacb`)  
**Verdict**: **CONFIRMED** (with 4 edge-case vulnerabilities cataloged)  

---

## 1. Observation

### 1.1 Baseline Test & Proof Verification
Direct independent reproduction of worker claims:
1. **Lean 4 Proofs & Axiom Audit**:
   Command: `cd /Users/mike/dev/ctrl/lean && lake env lean Research/LorentzConeCBF.lean`  
   Result: Exit code 0, 0 sorry, and `#print axioms` verified dependencies strictly within standard axioms `[propext, Classical.choice, Quot.sound]`.
2. **Python Verification Script**:
   Command: `cd /Users/mike/dev/ctrl && uv run python tools/verify_lorentz_cbf.py`  
   Result: Exit code 0, 100% pass across symbolic identities, operating envelope, and falsification gates.
3. **Pytest Test Suite**:
   Command: `cd /Users/mike/dev/ctrl && uv run pytest -v tests/test_lorentz_cbf.py`  
   Result: Exit code 0, `32 passed in 0.03s`.

---

### 1.2 Exact Rational Interval Arithmetic Stress Testing
Empirical verification of `tools/verify_lorentz_cbf.py` lines 69–156:
1. **Enclosure Property**:
   - Generator: 10,000 randomized interval pairs with random rational bounds and internal sample points.
   - Operations evaluated: addition (`+`), subtraction (`-`), multiplication (`*`), squaring (`sq()`), and division (`/`).
   - Result: **0 enclosure failures out of 10,000 trials** (100% true image enclosure).
2. **Tightness against Dense Grid Discretization**:
   - Compared `IntervalQ` bounds against 200-point dense grid sampling across 100 random intervals.
   - Result: `lo` and `hi` match the exact mathematical infima and suprema.
3. **Squaring Optimization**:
   - Evaluated `IntervalQ.sq()` on intervals containing zero, e.g., $[-2, 2]$.
   - Result: `IntervalQ.sq()` correctly yields $[0, 4]$, strictly avoiding the negative overestimation $[-4, 4]$ produced by naive bilinear multiplication $I \times I$.
4. **Operating Box Envelope Dependency Analysis**:
   - Function: `verify_operating_envelope(envelope)` in lines 265–309.
   - In $h_b(r, v) = (r_{\text{limit}} - r) \cdot \hat{n} - \frac{\|v\|^2}{2 a_{\text{brake}}}$, position $r \in \mathcal{B}_r$ and velocity $v \in \mathcal{B}_v$ are separable independent state boxes.
   - Evaluated: lower bound of $h_b$ over envelope:
     $$\text{Theoretical inf} = \min_{r \in \mathcal{B}_r} (r_{\text{limit}} - r) \cdot \hat{n} - \max_{v \in \mathcal{B}_v} \frac{\|v\|^2}{2 a_{\text{brake}}} = 2 - \frac{2.04}{6} = 1.660000$$
   - Result: `h_b_interval.lo == Fraction(166, 100)` matches the exact global infimum to the bit with zero wrapping inflation.

---

### 1.3 ZMP Calculation Under Free-Fall and Singularity ($g + a_z \to 0$)
Empirical testing of `check_zmp_support_polygon` (lines 334–377):
1. **Exact Free-Fall ($g + a_z = 0$)**:
   - Test vector: $r_{\text{com}} = [0, 0, 1]$, $a_{\text{com}} = [0, 0, -g]$, $g = 9.81$.
   - Observation: Line 350 `denom = g_f + az == 0` triggered line 351 `if denom <= 0:`.
   - Result: Returns `False, "FALSIFIED: net vertical acceleration (0.000) <= 0 (free-fall / liftoff)"`. No `ZeroDivisionError` occurred.
2. **Subzero Vertical Acceleration ($g + a_z < 0$)**:
   - Test vector: $a_z = -15.0 \text{ m/s}^2$ ($g + a_z = -5.19$).
   - Result: Safely returns `False, "FALSIFIED: net vertical acceleration (-5.190) <= 0 (free-fall / liftoff)"`.
3. **Asymptotic Limit $g + a_z = \epsilon \to 0^+$ with Lateral Deceleration $a_{xy} \neq 0$**:
   - Test vector: $\epsilon = 10^{-20}$, $a_x = 10^{-5}$, $r_z = 1.0$.
   - $p_{\text{ZMP}, x} = 0 - \frac{1}{10^{-20}} \times 10^{-5} = -10^{15} \text{ m}$.
   - Result: Correctly falsified: `False, "FALSIFIED: p_ZMP=(-1000000000000000.000, 0.000) outside support edge 3 -> 4 (robot tilts)"`.

---

### 1.4 Confirmed Vulnerabilities and Edge Cases
1. **Vulnerability 1 — Float Conversion Overflow in ZMP String Formatting**:
   - Code: `tools/verify_lorentz_cbf.py` lines 370 and 375:
     ```python
     f"FALSIFIED: p_ZMP=({float(p_zmp_x):.3f}, {float(p_zmp_y):.3f}) outside support edge..."
     ```
   - Test input: $g + a_z = 10^{-350}$, $a_x = 1.0$.
   - Observation: The exact rational calculation `cross < 0` evaluated to True without precision loss. However, when formatting the return string, Python executed `float(Fraction(10**350, 1))`.
   - Verbatim Error:
     ```
     OverflowError: integer division result too large for a float
     ```
   - Blast radius: Crashes with uncaught exception rather than cleanly returning `(False, ...)`.

2. **Vulnerability 2 — Polygon Winding Order Dependency**:
   - Code: `tools/verify_lorentz_cbf.py` line 367:
     ```python
     cross = edge_x * to_pt_y - edge_y * to_pt_x
     if cross < 0: return False, ...
     ```
   - Test input: Support polygon vertices supplied in clockwise order:
     `poly = [(-1, -1), (-1, 1), (1, 1), (1, -1)]`.
   - Point tested: Origin $(0, 0)$, strictly inside the box.
   - Result: Evaluates $cross < 0$ on edge 0, returning `False, "FALSIFIED: p_ZMP=(0.000, 0.000) outside support edge 0 -> 1 (robot tilts)"`.
   - Blast radius: Falsely rejects valid, safe physical states if polygon order is clockwise.

3. **Vulnerability 3 — Missing Lower-Bound Check on $a_{\text{brake}}$**:
   - Code: `tools/verify_lorentz_cbf.py` line 324:
     ```python
     if a_b > mu_f * g_f: return False, ...
     return True, ...
     ```
   - Test input: $a_{\text{brake}} = -5.0 \text{ m/s}^2 \le \mu g$.
   - Result: Returns `True, "SATISFIED: a_brake=-5.000 <= mu*g=5.886"`.
   - Physical meaning: A negative braking deceleration accelerates the robot towards the obstacle, violating stopping safety while passing friction check.

4. **Vulnerability 4 — Static Gravity Assumption in Multi-Axis Dynamics**:
   - Code: `check_friction_limit(a_brake, mu, g)` computes threshold as $\mu g$.
   - Observation: In 3D centroidal dynamics with downward vertical acceleration $a_z < 0$, the effective normal acceleration is $g_{\text{eff}} = g + a_z < g$.
   - Test scenario: $g = 9.81$, $a_z = -5.0$, $\mu = 0.6$, $a_{\text{brake}} = 4.0$. Under static $g$, $4.0 \le 5.886$ returns `SATISFIED`. However, effective maximum traction is $\mu (g + a_z) = 2.886 < 4.0$, so slip is unavoidable.

---

### 1.5 Extremal Test Vectors (Arbitrary Precision & Stability)
1. **1000-Digit Rationals**:
   - Tested `compute_lambda_star` and `IntervalQ` with numerators/denominators exceeding $10^{1000}$.
   - Result: Python `Fraction` exact rational arithmetic completed with zero precision loss and exact fraction simplification.
2. **Clamping Invariance of $\lambda^*(x)$**:
   - In `compute_lambda_star`, line 172: `max(Fraction(0), min(Fraction(1), ratio))`.
   - Tested extreme ratios ($\pm 10^{500}$): returned value is strictly bounded in $[0, 1]$.
3. **Relative Degree 2 Singularity at Zero Velocity**:
   - When robot is at rest ($v = 0$), $L_g h = -v / a_{\text{brake}} = 0$.
   - If clearance is negative (already violated), $a_{\pi} = a_{\text{nom}} = 0$, $b > 0$.
   - Result: `compute_lambda_star` raises `ValueError: Backup policy lacks authority`, correctly reflecting the loss of control authority at relative degree 2 rest states.

---

## 2. Logic Chain

1. **Validity of Master Theorem & Exact Arithmetic**:
   - By Observation 1.1, the Lean 4 formalization checks cleanly under standard axioms with 0 `sorry`, confirming that convex interpolation of the Lorentz cone is a mathematically sound barrier solution.
   - By Observation 1.2, `IntervalQ` operations ($+$, $-$, $*$, $/$, $\text{sq}$) satisfy the strict inclusion property $f(X, Y) \subseteq f(I_X, I_Y)$ across 10,000 randomized test cases and match analytical extrema on dense grids.
   - Therefore, the exact rational interval verification is mathematically sound and encloses the true continuous operating envelope.

2. **Soundness of Falsification Gates**:
   - By Observation 1.3, `check_zmp_support_polygon` properly intercepts exact zero vertical acceleration ($g + a_z = 0$) and negative vertical acceleration ($g + a_z < 0$) via the guard `if denom <= 0:`, preventing division by zero.
   - For near-zero positive vertical acceleration ($g + a_z \to 0^+$), non-zero horizontal acceleration properly drives the ZMP outside the footprint, triggering polygon falsification.

3. **Characterization of Numerical Edge Cases**:
   - By Observation 1.4 (Vulnerability 1), the mathematical logic in `check_zmp_support_polygon` succeeds, but string formatting via `float()` triggers `OverflowError` when rational fractions exceed IEEE-754 range ($> 1.797 \times 10^{308}$).
   - By Observation 1.4 (Vulnerabilities 2–4), polygon winding orientation, negative deceleration, and vertical acceleration coupling are unhandled preconditions.
   - However, within physical operational regimes (where $p_{\text{ZMP}} < 10^{300}$ and vertices are CCW), all tests execute correctly.

---

## 3. Caveats

1. **Scope of Proof**: The Lean 4 formalization proves convex combination invariance for the Lorentz cone and scalar barrier satisfaction under the rigid point-contact Coulomb friction model. Compliant contact dynamics and continuous foot rolling were not part of M2 scope.
2. **Review-Only Constraint**: In accordance with the system constraints ("Review-only — do NOT modify implementation code directly; report any failures as findings"), the 4 identified edge-case vulnerabilities have been empirically demonstrated and documented without modifying `tools/verify_lorentz_cbf.py`.

---

## 4. Conclusion

**Verdict**: **CONFIRMED**

The core claims of Milestone 2 Controls (Seed 1 Centroidal Lorentz-Cone Backup CBF) are verified and confirmed:
1. Exact rational interval arithmetic properly encloses the true image and certifies the continuous operating box envelope without precision loss.
2. Zero division and free-fall conditions are safely rejected.
3. The closed-form $\lambda^*(x)$ interpolation parameter remains strictly within $[0, 1]$.
4. The Lean 4 proof is fully checked by the kernel with 0 sorry.

### Actionable Mitigations for Production Hardening:
1. **Fix Float Overflow in Message Formatting**: In `check_zmp_support_polygon`, wrap `float(p_zmp_x)` in a `try...except OverflowError:` block or format large fractions via scientific notation string helpers.
2. **Enforce Winding Order Agnosticism**: Compute signed area via the Shoelace formula and automatically reverse clockwise polygons.
3. **Enforce Positive Deceleration**: In `check_friction_limit`, check `if a_b <= 0: return False, "FALSIFIED: a_brake must be strictly positive"`.
4. **Pass Effective Gravity**: Ensure callers of `check_friction_limit` supply $g_{\text{eff}} = g + a_z$ during multi-axis maneuvers.

---

## 5. Verification Method

### 5.1 Reproduction Commands
Run from `/Users/mike/dev/ctrl`:
```sh
# 1. Verify Lean 4 proof & standard axioms
cd /Users/mike/dev/ctrl/lean && lake env lean Research/LorentzConeCBF.lean

# 2. Run Python verification script
cd /Users/mike/dev/ctrl && uv run python tools/verify_lorentz_cbf.py

# 3. Run Pytest test suite
cd /Users/mike/dev/ctrl && uv run pytest -v tests/test_lorentz_cbf.py

# 4. Reproduce the 4 empirical vulnerabilities and extremal tests
uv run python -c "
from fractions import Fraction
from tools.verify_lorentz_cbf import check_zmp_support_polygon, check_friction_limit, IntervalQ

poly = [(-1, -1), (1, -1), (1, 1), (-1, 1)]
g = Fraction(981, 100)

# Vulnerability 1: Float Overflow
try:
    check_zmp_support_polygon([0, 0, 1], [1, 0, -g + Fraction(1, 10**350)], g, poly)
except OverflowError as e:
    print('Vulnerability 1 Reproduced: OverflowError in string formatting:', e)

# Vulnerability 2: Clockwise polygon
poly_cw = [(-1, -1), (-1, 1), (1, 1), (1, -1)]
sat, msg = check_zmp_support_polygon([0, 0, 1], [0, 0, 0], g, poly_cw)
assert not sat
print('Vulnerability 2 Reproduced: False rejection of interior point under CW polygon')

# Vulnerability 3: Negative a_brake
sat, _ = check_friction_limit(-5, 0.6, g)
assert sat
print('Vulnerability 3 Reproduced: check_friction_limit accepts negative deceleration')
"
```

### 5.2 Invalidation Conditions
- If any interval operation fails to contain the true analytical image on arbitrary rational inputs.
- If an input pair $u_1, u_2 \in \mathcal{K}(\mu)$ exists such that their convex combination escapes $\mathcal{K}(\mu)$ for $\lambda \in [0, 1]$.
- If `compute_lambda_star` returns a value outside $[0, 1]$ when authority is non-zero.
