"""Adversarial Stress Test Suite for Centroidal Lorentz-Cone Backup CBF.

Written by challenger_m2_1 to empirically test:
1. Cone convexity counterexamples: boundary, orthogonal, extreme aspect ratios.
2. Grazing and corner cases: u_z = 0, boundary vectors, a(x) . pi_b = a(x) . u_nom.
3. Bounds of lambda*(x): negative or > 1 when valid backup exists.
"""

from __future__ import annotations

import math
import random
import sys
from fractions import Fraction
from pathlib import Path

# Add repo root to path
REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.verify_lorentz_cbf import (  # noqa: E402
    Vec3Q,
    compute_lambda_star,
    interpolated_control,
    verify_conic_convexity_decomposition,
)


def run_convexity_attacks(num_random_trials: int = 50000) -> dict:
    """Attempt to construct counterexamples to cone convexity.

    Returns dict of statistics and any counterexamples found.
    """
    failures = []
    tests_run = 0

    print("--- [Attack 1] Cone Convexity Stress Tests ---")

    # 1.1 Extreme aspect ratios mu
    extreme_mus = [
        Fraction(1, 10**18),
        Fraction(1, 10**6),
        Fraction(1, 1000),
        Fraction(1, 100),
        Fraction(1, 10),
        Fraction(1, 2),
        Fraction(1),
        Fraction(2),
        Fraction(10),
        Fraction(100),
        Fraction(10**6),
        Fraction(10**18),
        Fraction(0),  # Degenerate zero friction
    ]

    pyth_directions = [
        (Fraction(1), Fraction(0)),
        (Fraction(-1), Fraction(0)),
        (Fraction(0), Fraction(1)),
        (Fraction(0), Fraction(-1)),
        (Fraction(3, 5), Fraction(4, 5)),
        (Fraction(-3, 5), Fraction(4, 5)),
        (Fraction(3, 5), Fraction(-4, 5)),
        (Fraction(-3, 5), Fraction(-4, 5)),
        (Fraction(5, 13), Fraction(12, 13)),
        (Fraction(7, 25), Fraction(24, 25)),
        (Fraction(8, 17), Fraction(15, 17)),
    ]

    z_values = [
        Fraction(0),
        Fraction(1, 10**12),
        Fraction(1, 1000),
        Fraction(1),
        Fraction(1000),
        Fraction(10**12),
    ]

    lambdas = [
        Fraction(0),
        Fraction(1, 10**9),
        Fraction(1, 1000),
        Fraction(1, 10),
        Fraction(1, 4),
        Fraction(1, 2),
        Fraction(3, 4),
        Fraction(9, 10),
        Fraction(999, 1000),
        Fraction(10**9 - 1, 10**9),
        Fraction(1),
    ]

    for mu in extreme_mus:
        for z1 in z_values:
            for z2 in z_values:
                for dx1, dy1 in pyth_directions:
                    # u1 on boundary
                    u1 = Vec3Q(mu * z1 * dx1, mu * z1 * dy1, z1)
                    assert u1.in_lorentz_cone(mu), f"u1 boundary construction failed for mu={mu}, z1={z1}"

                    for dx2, dy2 in pyth_directions:
                        # u2 on boundary
                        u2 = Vec3Q(mu * z2 * dx2, mu * z2 * dy2, z2)
                        assert u2.in_lorentz_cone(mu), f"u2 boundary construction failed for mu={mu}, z2={z2}"

                        for lam in lambdas:
                            tests_run += 1
                            w = (Fraction(1) - lam) * u1 + lam * u2
                            if not w.in_lorentz_cone(mu):
                                failures.append({
                                    "type": "boundary_convex_combination",
                                    "mu": mu,
                                    "u1": u1,
                                    "u2": u2,
                                    "lam": lam,
                                    "w": w,
                                    "margin": w.lorentz_margin(mu),
                                    "w_z": w.z,
                                })
                            # Check margin decomposition identity
                            if not verify_conic_convexity_decomposition(u1, u2, mu, lam):
                                failures.append({
                                    "type": "margin_decomposition_mismatch",
                                    "mu": mu,
                                    "u1": u1,
                                    "u2": u2,
                                    "lam": lam,
                                })

    print(f"  Completed {tests_run} structured boundary & extreme aspect ratio checks.")

    # 1.2 Randomized fuzzing of cone vectors
    random.seed(42)
    rand_tests = 0
    for _ in range(num_random_trials):
        # Sample random mu in [1e-6, 1e6]
        log_mu = random.uniform(-6, 6)
        mu = Fraction(int(10 ** (log_mu + 6)), 10**6)

        # Sample random z1, z2 >= 0
        z1 = Fraction(random.randint(0, 10000), 100)
        z2 = Fraction(random.randint(0, 10000), 100)

        # Sample (x1, y1) such that x1^2 + y1^2 <= mu^2 * z1^2
        r1_ratio = Fraction(random.randint(0, 1000), 1000)  # [0, 1]
        theta1 = random.uniform(0, 2 * math.pi)
        x1 = Fraction(int(float(mu * z1 * r1_ratio) * math.cos(theta1) * 1000), 1000)
        y1 = Fraction(int(float(mu * z1 * r1_ratio) * math.sin(theta1) * 1000), 1000)
        while x1 * x1 + y1 * y1 > (mu * mu) * (z1 * z1):
            x1 = x1 * Fraction(999, 1000)
            y1 = y1 * Fraction(999, 1000)

        u1 = Vec3Q(x1, y1, z1)

        r2_ratio = Fraction(random.randint(0, 1000), 1000)
        theta2 = random.uniform(0, 2 * math.pi)
        x2 = Fraction(int(float(mu * z2 * r2_ratio) * math.cos(theta2) * 1000), 1000)
        y2 = Fraction(int(float(mu * z2 * r2_ratio) * math.sin(theta2) * 1000), 1000)
        while x2 * x2 + y2 * y2 > (mu * mu) * (z2 * z2):
            x2 = x2 * Fraction(999, 1000)
            y2 = y2 * Fraction(999, 1000)

        u2 = Vec3Q(x2, y2, z2)

        lam = Fraction(random.randint(0, 10000), 10000)

        rand_tests += 1
        w = (Fraction(1) - lam) * u1 + lam * u2
        if not w.in_lorentz_cone(mu):
            failures.append({
                "type": "random_fuzz_convex_combination",
                "mu": mu,
                "u1": u1,
                "u2": u2,
                "lam": lam,
                "w": w,
            })

    print(f"  Completed {rand_tests} randomized fuzzing trials.")
    return {
        "tests_run": tests_run + rand_tests,
        "failures_count": len(failures),
        "failures": failures,
    }


def run_grazing_and_corner_attacks() -> dict:
    """Test grazing and corner cases:

    - u_z = 0
    - boundary vectors (u_x^2 + u_y^2 = mu^2 u_z^2)
    - a(x) . pi_b(x) = a(x) . u_nom(x)
    """
    failures = []
    tests_run = 0

    print("--- [Attack 2] Grazing and Corner Cases ---")

    # 2.1 Case u_z = 0
    # Any vector in cone with u_z = 0 must have u_x = 0, u_y = 0
    mu = Fraction(6, 10)
    origin = Vec3Q.from_values(0, 0, 0)
    assert origin.in_lorentz_cone(mu)
    assert origin.lorentz_margin(mu) == Fraction(0)

    # Check non-zero vectors with u_z = 0: must NEVER be in cone
    for dx, dy in [(1, 0), (0, 1), (-1, 0), (0, -1), (1, 1), (Fraction(1, 1000), 0)]:
        u_grazing = Vec3Q.from_values(dx, dy, 0)
        tests_run += 1
        if u_grazing.in_lorentz_cone(mu):
            failures.append({
                "type": "nonzero_uz_zero_in_cone",
                "vector": u_grazing,
            })

    # Convex combination between origin and any cone vector
    for z in [Fraction(1, 10), Fraction(1), Fraction(100)]:
        u_interior = Vec3Q.from_values(0, 0, z)
        u_boundary = Vec3Q.from_values(mu * z, 0, z)
        for lam in [Fraction(0), Fraction(1, 2), Fraction(1)]:
            tests_run += 2
            w1 = (Fraction(1) - lam) * origin + lam * u_interior
            w2 = (Fraction(1) - lam) * origin + lam * u_boundary
            if not w1.in_lorentz_cone(mu):
                failures.append({"type": "origin_interp_interior", "lam": lam, "w": w1})
            if not w2.in_lorentz_cone(mu):
                failures.append({"type": "origin_interp_boundary", "lam": lam, "w": w2})

    print(f"  Verified u_z = 0 apex uniqueness and combinations ({tests_run} checks).")

    # 2.2 Boundary vectors: u_x^2 + u_y^2 = mu^2 u_z^2
    # Check that combination of distinct boundary rays lies strictly in the interior
    b_tests = 0
    pyth = [
        (Fraction(1), Fraction(0)),
        (Fraction(0), Fraction(1)),
        (Fraction(-1), Fraction(0)),
        (Fraction(0), Fraction(-1)),
        (Fraction(3, 5), Fraction(4, 5)),
        (Fraction(-3, 5), Fraction(4, 5)),
        (Fraction(5, 13), Fraction(12, 13)),
    ]
    for d1 in pyth:
        for d2 in pyth:
            u1 = Vec3Q(mu * 5 * d1[0], mu * 5 * d1[1], Fraction(5))
            u2 = Vec3Q(mu * 5 * d2[0], mu * 5 * d2[1], Fraction(5))
            assert u1.lorentz_margin(mu) == 0
            assert u2.lorentz_margin(mu) == 0

            for lam in [Fraction(1, 4), Fraction(1, 2), Fraction(3, 4)]:
                b_tests += 1
                w = (Fraction(1) - lam) * u1 + lam * u2
                m = w.lorentz_margin(mu)
                if d1 == d2:
                    # Same ray: margin is zero
                    if m != 0:
                        failures.append({"type": "same_ray_boundary_margin_nonzero", "m": m})
                else:
                    # Distinct rays: strictly interior
                    if m <= 0:
                        failures.append({"type": "distinct_rays_not_interior", "m": m, "d1": d1, "d2": d2})

    print(f"  Verified boundary chord interiority: {b_tests} exact checks.")

    # 2.3 Case: a(x) . pi_b(x) == a(x) . u_nom(x)
    authority_tests = 0
    a_cbf = Vec3Q.from_values(1, 0, 0)
    u_nom = Vec3Q.from_values(2, 0, 5)  # a_nom = 2
    pi_b = Vec3Q.from_values(2, 1, 6)   # a_pi = 2
    assert a_cbf.dot(u_nom) == a_cbf.dot(pi_b) == Fraction(2)

    # Subcase A: b <= a_nom (nominal already safe)
    for b in [Fraction(0), Fraction(1), Fraction(2)]:
        authority_tests += 1
        lam = compute_lambda_star(b, a_cbf.dot(u_nom), a_cbf.dot(pi_b))
        if lam != 0:
            failures.append({"type": "equal_authority_safe_nominal_nonzero_lam", "b": b, "lam": lam})
        u_safe = interpolated_control(u_nom, pi_b, lam)
        if not (a_cbf.dot(u_safe) >= b):
            failures.append({"type": "equal_authority_safe_nominal_barrier_failed", "b": b})

    # Subcase B: b > a_nom (nominal is unsafe)
    for b in [Fraction(21, 10), Fraction(3), Fraction(10)]:
        authority_tests += 1
        raised = False
        try:
            compute_lambda_star(b, a_cbf.dot(u_nom), a_cbf.dot(pi_b))
        except ValueError:
            raised = True
        if not raised:
            failures.append({"type": "equal_authority_unsafe_nominal_did_not_raise", "b": b})

    print(f"  Verified equal authority cases (a . pi_b == a . u_nom): {authority_tests} checks.")

    return {
        "tests_run": tests_run + b_tests + authority_tests,
        "failures_count": len(failures),
        "failures": failures,
    }


def run_lambda_bounds_attacks(num_trials: int = 50000) -> dict:
    """Verify whether lambda*(x) can EVER be negative or > 1 when a valid backup exists.

    Valid backup exists means:
    1. u_nom in K(mu)
    2. pi_b in K(mu)
    3. a(x) . pi_b >= b
    """
    failures = []
    tests_run = 0

    print("--- [Attack 3] Lambda*(x) Bounds Stress Tests ---")

    # Systematic grid over relationship between b, a_nom, a_pi
    # When valid backup exists, b <= a_pi.
    test_cases = [
        # (b, a_nom, a_pi)
        (Fraction(0), Fraction(0), Fraction(1)),
        (Fraction(0), Fraction(-5), Fraction(0)),
        (Fraction(5), Fraction(0), Fraction(5)),
        (Fraction(3), Fraction(1), Fraction(5)),
        (Fraction(1, 10**6), Fraction(0), Fraction(1)),
        (Fraction(1 - 10**-6), Fraction(0), Fraction(1)),
        (Fraction(10**6), Fraction(-10**6), Fraction(10**6)),
        (-Fraction(10**6), -Fraction(10**7), -Fraction(10**6)),
    ]

    for b, a_nom, a_pi in test_cases:
        tests_run += 1
        # b <= a_pi holds by construction
        lam = compute_lambda_star(b, a_nom, a_pi)
        if lam < 0 or lam > 1:
            failures.append({
                "type": "lambda_out_of_bounds_grid",
                "b": b, "a_nom": a_nom, "a_pi": a_pi, "lam": lam,
            })

    # Randomized fuzzing: sample valid setups
    random.seed(1337)
    for _ in range(num_trials):
        a_pi_val = random.uniform(-1000, 1000)
        b_val = a_pi_val - random.uniform(0, 1000)
        a_nom_val = random.uniform(-2000, 2000)

        a_pi = Fraction(int(a_pi_val * 100), 100)
        b = Fraction(int(b_val * 100), 100)
        a_nom = Fraction(int(a_nom_val * 100), 100)

        if b > a_pi:
            b, a_pi = a_pi, b

        tests_run += 1
        try:
            lam = compute_lambda_star(b, a_nom, a_pi)
            if lam < Fraction(0) or lam > Fraction(1):
                failures.append({
                    "type": "lambda_out_of_bounds_random",
                    "b": b, "a_nom": a_nom, "a_pi": a_pi, "lam": lam,
                })
        except ValueError as e:
            if not (b > a_nom and a_pi <= a_nom):
                failures.append({
                    "type": "unexpected_value_error",
                    "b": b, "a_nom": a_nom, "a_pi": a_pi, "error": str(e),
                })

    print(f"  Completed {tests_run} lambda* validity and boundary tests.")
    return {
        "tests_run": tests_run,
        "failures_count": len(failures),
        "failures": failures,
    }


def main():
    print("=" * 70)
    print("CHALLENGER M2: ADVERSARIAL STRESS TEST HARNESS")
    print("=" * 70)

    res1 = run_convexity_attacks(num_random_trials=20000)
    res2 = run_grazing_and_corner_attacks()
    res3 = run_lambda_bounds_attacks(num_trials=20000)

    total_tests = res1["tests_run"] + res2["tests_run"] + res3["tests_run"]
    total_failures = res1["failures_count"] + res2["failures_count"] + res3["failures_count"]

    print("\n" + "=" * 70)
    print("ADVERSARIAL STRESS TEST SUMMARY")
    print(f"Total tests executed: {total_tests}")
    print(f"Total failures / counterexamples found: {total_failures}")
    print("=" * 70)

    if total_failures == 0:
        print("VERDICT: CONFIRMED (Solution holds against all adversarial attacks)")
    else:
        print("VERDICT: DISPROVED (Counterexamples detected!)")
        sys.exit(1)


if __name__ == "__main__":
    main()
