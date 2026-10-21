"""Quartic y^2=g(x) -> Weierstrass model with explicit inverse map to x (see bigx.py docstring)."""
from fractions import Fraction as Fr
from families import pari


def fr(g):
    return Fr(int(pari.numerator(g)), int(pari.denominator(g)))


def weier(c0, Fp):
    """Return (E, to_x) for y^2 = c0*F(x) quartic, using a rational point moved to infinity."""
    g = c0 * Fp
    pts = pari.hyperellratpoints(g, 200)
    lead = pari.polcoef(g, 4)
    shift = None
    if not pari.issquare(lead):
        for p in pts:
            if p[1] != 0:
                shift = p[0]
                break
        if shift is None:
            return None
        g2 = pari.simplify(pari("x^4") * pari.subst(g, "x", pari(f"{shift} + 1/x")))
    else:
        g2 = g
    lc = pari.polcoef(g2, 4)
    mon = g2 / lc
    b, c, d, e = [pari.polcoef(mon, k) for k in (3, 2, 1, 0)]
    E = pari.ellinit([0, c, 0, b * d - 4 * e, d * d + b * b * e - 4 * c * e])

    def to_x(P):
        if len(P) == 1:
            return None
        T, S = P[0], P[1]
        t = -T / 2
        den = 2 * (b * b / 4 + 2 * t - c)
        if den == 0:
            return None
        xx = (S - (b * t - d)) / den
        if shift is not None:
            if xx == 0:
                return None
            xx = shift + 1 / xx
        return fr(xx)

    return E, to_x


