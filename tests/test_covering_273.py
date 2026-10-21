"""Test suite for Erdős Problem 273 covering system certificates.

Verifies independent audit replays and adversarial mutation checks for both
the 7-smooth kernel certificate (check_seven.py) and the 11-smooth extension
certificate (check_eleven.py).
"""

import runpy
from fractions import Fraction
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
CHECKER_7 = runpy.run_path(str(ROOT / "work/273/check_seven.py"))
CHECKER_11 = runpy.run_path(str(ROOT / "work/273/check_eleven.py"))


def test_independent_seven_certificate_and_mutation_rejection():
    """Verify 7-smooth covering certificate and 4 corrupted certificate rejections."""
    result = CHECKER_7["check"](CHECKER_7["MASS_BOUNDS"], CHECKER_7["MIN_GAP"])
    assert result["checked"] is True
    assert result["checked_assignments"] == 720
    assert result["minimum_density_margin"] == "57/10000"
    assert CHECKER_7["mutation_checks"]() == 4


def test_independent_eleven_certificate_replay():
    """Verify 11-smooth covering certificate replayed across 3,518 tree nodes."""
    result = CHECKER_11["check"]()
    assert result["checked"] is True
    assert result["retained_count"] == 5265
    assert result["exact_geometric_tail"] == "1806085527193/7116137582400000"
    assert result["unconditioned_density"] == "728347923255532331431/619957906178688000000"
    assert result["tree_stats"]["nodes"] == 3518
    assert result["tree_stats"]["pruned"] == 3271
    assert result["tree_stats"]["unresolved"] == 0
    assert result["tree_stats"]["memo_hits"] == 2614
    assert result["minimum_prune_gap"] == "50661803066306609/1239915812357376000000"
    assert result["min_survivors"] >= 212
    assert result["excluded_by_capacity_tree"] is True


def test_eleven_mutation_checks_rejection():
    """Ensure all 4 adversarial mutations are rejected by mutation_checks()."""
    rejected = CHECKER_11["mutation_checks"]()
    assert rejected == 4


def test_eleven_rejects_mutated_root_period():
    """Adversarial mutation 1a: Mutate root period away from lcm(prefix)."""
    with pytest.raises(ValueError, match="period.*must equal lcm"):
        CHECKER_11["check"](period=360)


def test_eleven_rejects_mutated_prefix_modulus():
    """Adversarial mutation 1b: Mutate prefix moduli by dropping or corrupting elements."""
    with pytest.raises(ValueError, match="unexpected prefix moduli"):
        CHECKER_11["check"](prefix=(4, 6, 10, 12, 16, 18, 30))


def test_eleven_rejects_tampered_node_capacity_bound():
    """Adversarial mutation 2: Artificial inflation of tree node capacity bound."""
    with pytest.raises(ValueError, match="capacity bias must be zero|density gap.*below certified minimum margin"):
        CHECKER_11["check"](capacity_bias=1000)


def test_eleven_rejects_tampered_geometric_tail():
    """Adversarial mutation 3: Tamper with geometric tail bound outside exponent box."""
    tampered_tail = CHECKER_11["EXPECTED_TAIL"] + Fraction(1, 1000)
    with pytest.raises(ValueError, match="geometric tail bound mismatch"):
        CHECKER_11["check"](tail_bound=tampered_tail)


def test_eleven_rejects_mutated_branch_residue_offset():
    """Adversarial mutation 4: Mutate branch residue offset away from canonical stabilizer orbits."""
    with pytest.raises(ValueError, match="branch offset must be zero|branch residue.*outside canonical orbit range"):
        CHECKER_11["check"](branch_offset=1)


def test_exact_5prime_geometric_tail_computation():
    """Verify exact rational geometric tail computation matches known closed form."""
    tail = CHECKER_11["compute_geometric_tail"](CHECKER_11["PRIMES"], CHECKER_11["CAPS"])
    assert tail == Fraction(1806085527193, 7116137582400000)
    assert 0 < tail < Fraction(3, 10000)


def test_admissible_pool_structure():
    """Verify exponent box generation and Fermat sieve properties."""
    pool = CHECKER_11["compute_admissible_pool"](CHECKER_11["PRIMES"], CHECKER_11["CAPS"])
    assert len(pool) == 5265
    assert all(m % 2 == 0 for m in pool)
    assert all(m >= 4 for m in pool)
    assert set(CHECKER_11["PREFIX"]).issubset(set(pool))


def test_erdos_273_variants_three_strict_covering_system():
    """Verify the 12-modulus strict covering system for primes p >= 3 in Erdos273.lean."""
    mods = [2, 4, 6, 10, 12, 18, 30, 36, 40, 60, 72, 180]
    res = [1, 0, 0, 0, 2, 4, 4, 10, 2, 46, 70, 178]
    primes = [3, 5, 7, 11, 13, 19, 31, 37, 41, 61, 73, 181]
    assert len(mods) == len(set(mods)) == 12
    for m, r, p in zip(mods, res, primes, strict=True):
        assert p >= 3
        assert all(p % d != 0 for d in range(2, int(p**0.5) + 1))
        assert m == p - 1
        assert 0 <= r < m
        assert 360 % m == 0
    for n in range(360):
        assert any(n % m == r for m, r in zip(mods, res, strict=True))
