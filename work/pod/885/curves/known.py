"""Known grids U+V subset of squares (rows U, columns V), as exact Fractions."""
from fractions import Fraction as F
from math import isqrt


def is_sq(x):
    x = F(x)
    if x < 0:
        return False
    n, d = x.numerator, x.denominator
    return isqrt(n) ** 2 == n and isqrt(d) ** 2 == d


def sqrtq(x):
    x = F(x)
    return F(isqrt(x.numerator), isqrt(x.denominator))


def check(U, V):
    return all(is_sq(F(u) + F(v)) for u in U for v in V)


KNOWN = {
    "lagrange44": ([324, 54756, 119716, 264196], [0, 79200, 227205, 1258560]),
    "pan54": ([202720644, 827712900, 1476864900, 494706564, 80729856900],
              [0, 358400700, 1398239500, 17139008700]),
    "mausberg54": ([z * z for z in (330, 870, 2445, 4155, 10482)],
                   [0, 756000, 15971200, 45130176]),
    "aleks54": ([0] + [4 * n for n in (515504, 3542528, 6010004, 19523504)],
                [d * d for d in (872, 4328, 5003, 11672)]),
    "chou44a": ([44782864, 340218025, 1738222864, 2777290000], [0, 25777136, 1222007600, 1719217136]),
    "chou44b": ([14400, 266256, 435600, 12110400], [0, 104625, 223744, 12096000]),
    "chou53": ([198916, 532900, 1674436, 13468900, 19404025], [0, 3588000, 8527200]),
}

if __name__ == "__main__":
    for k, (U, V) in KNOWN.items():
        print(k, len(U), "x", len(V), check(U, V))
