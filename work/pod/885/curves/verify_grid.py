"""Independent exact verifier for grids U+V subset of squares (Fractions only, no floats).

Checks: every u+v is the square of a rational; rows distinct; columns distinct.
Then normalises to the integer form of Erdos #885 (rows -> N's, columns -> d's) for both
orientations and re-verifies by direct divisor enumeration of D(N) = {|a-b| : ab = N}.

usage: python verify_grid.py grid.json   (json: {"U": [...], "V": [...]}, entries as "p/q" strings)
"""
import json, sys
from fractions import Fraction as F
from math import isqrt, lcm


def is_sq(x):
    if x < 0:
        return False
    return isqrt(x.numerator) ** 2 == x.numerator and isqrt(x.denominator) ** 2 == x.denominator


def check_grid(U, V):
    assert len(set(U)) == len(U), "rows not distinct"
    assert len(set(V)) == len(V), "columns not distinct"
    for u in U:
        for v in V:
            assert is_sq(u + v), f"{u}+{v} not a square"
    return True


def integer_form(U, V):
    """Rows U (m), columns V (n) -> (m-1) integers N sharing n differences d.
    u0 = min U; N_i = (u_i-u0)/4, d_j = sqrt(u0+v_j), all scaled by a common square."""
    U = sorted(U)
    u0 = U[0]
    vals = [u - u0 for u in U[1:]] + [u0 + v for v in V]
    den = 1
    for x in vals:
        den = lcm(den, x.denominator)
    # smallest k with k^2 * den-multiple: take k = product over primes of den of p^ceil(e/2)
    k, n = 1, den
    p = 2
    while p * p <= n:
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        k *= p ** ((e + 1) // 2)
        p += 1
    if n > 1:
        k *= n
    S = F(4 * k * k)  # factor 4 so that N = (u-u0)/4 is integral
    Ns = [int((u - u0) * S) // 4 for u in U[1:]]
    for u in U[1:]:
        assert ((u - u0) * S).denominator == 1 and int((u - u0) * S) % 4 == 0
    ds = []
    for v in V:
        w = (u0 + v) * S
        assert w.denominator == 1 and is_sq(w)
        ds.append(isqrt(int(w)))
    return Ns, ds


def D(n):
    out, a = set(), 1
    while a * a <= n:
        if n % a == 0:
            out.add(n // a - a)
        a += 1
    return out


def D_member(n, d):
    """d in D(n) iff 4n + d^2 is a square (exact)."""
    s = 4 * n + d * d
    r = isqrt(s)
    return r * r == s and (r - d) % 2 == 0 and r > d


def verify(U, V, enumerate_divisors=True):
    U = [F(u) for u in U]
    V = [F(v) for v in V]
    check_grid(U, V)
    print(f"grid {len(U)}x{len(V)}: all {len(U)*len(V)} sums are rational squares; rows/cols distinct")
    for name, (A, B) in (("rows->N", (U, V)), ("cols->N", (V, U))):
        Ns, ds = integer_form(A, B)
        assert len(set(Ns)) == len(Ns) and all(n > 0 for n in Ns)
        assert len(set(ds)) == len(ds) and all(d > 0 for d in ds), "a difference is 0 or repeated"
        for n in Ns:
            for d in ds:
                assert D_member(n, d), (n, d)
        print(f" {name}: {len(Ns)} N's share {len(ds)} differences  N={Ns}  d={ds}")
        if enumerate_divisors and max(Ns) < 10**13:
            common = set.intersection(*[D(n) for n in Ns])
            assert set(ds) <= common
            print(f"   divisor enumeration: |intersection D(N_i)| = {len(common)} >= {len(ds)} OK")
    return True


if __name__ == "__main__":
    g = json.load(open(sys.argv[1]))
    verify(g["U"], g["V"], enumerate_divisors=("--noenum" not in sys.argv))
