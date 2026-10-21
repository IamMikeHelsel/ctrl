"""Check the grid <-> common-difference equivalence on Pan's published 5x4 grid."""

from fractions import Fraction
from math import isqrt


def is_sq(x: Fraction) -> bool:
    if x < 0:
        return False
    n, d = x.numerator, x.denominator
    return isqrt(n) ** 2 == n and isqrt(d) ** 2 == d


def D(n: int) -> set[int]:
    out, a = set(), 1
    while a * a <= n:
        if n % a == 0:
            out.add(n // a - a)
        a += 1
    return out


def to_integer_form(rows, cols):
    """Normalise by the smallest row: N_i = (u_i - u_0)/4, d_j = sqrt(u_0 + v_j)."""
    rows = sorted(rows)
    u0 = rows[0]
    ds = [isqrt((u0 + v).numerator) for v in cols]
    scale = 1
    for v in cols:
        assert is_sq(u0 + v)
        scale = max(scale, (u0 + v).denominator)
    Ns = [(u - u0) for u in rows[1:]]
    # clear denominators by a common square factor, then make 4 | (u - u0)
    from math import lcm

    den = 1
    for x in Ns + [u0 + v for v in cols]:
        den = lcm(den, x.denominator)
    sq = 1
    while (sq * sq) % den:
        sq += 1
    k = sq * sq * 4
    Ns = [int(x * k) // 4 for x in Ns]
    ds = [isqrt(int((u0 + v) * k)) for v in cols]
    return Ns, ds


A = [202720644, 827712900, 1476864900, 494706564, 80729856900]
B = [0, 358400700, 1398239500, 17139008700]
U = [Fraction(a) for a in A]
V = [Fraction(b) for b in B]
assert all(is_sq(u + v) for u in U for v in V)

for name, rows, cols in [("rows=A", U, V), ("rows=B (transposed)", V, U)]:
    Ns, ds = to_integer_form(rows, cols)
    common = set.intersection(*(D(n) for n in Ns)) if all(n < 10**13 for n in Ns) else None
    print(name, "->", len(Ns), "N's sharing", len(ds), "d's")
    print("  N =", Ns)
    print("  d =", sorted(ds))
    ok = all(isqrt(4 * n + d * d) ** 2 == 4 * n + d * d for n in Ns for d in ds)
    print("  all 4N+d^2 squares:", ok)
