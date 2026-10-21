"""Search Klein-four (V) configurations: columns C_j = c_j (x^2-u_j^2)(x^2-d^2/u_j^2), u1 = 1, plus 0.

V = <x->-x, x->d/x>; pairing planes P1 = <x^2,1>, P2 = <x^2+d, x>, P3 = <x^2-d, x>.
Rows a = A e1 + B e2 valid on both columns:
  P2: B^2 - s_j^2 A^2 = c_j s_j^2, s_j = u_j + d/u_j      (2 rows if A^2, c1+A^2 squares)
  P3: same with s_j' = u_j - d/u_j
  P1: B^2 + sig_j A B + d^2 A^2 = K_j, sig_j = u_j^2+d^2/u_j^2, K_j = c_j (u_j^2-d^2/u_j^2)^2/4
P2 is forced to have 2 rows by c2 = (c1 s1^2 - A^2 (s2^2 - s1^2))/s2^2, A = (c1-m^2)/(2m).
usage: vsearch.py H idx nproc   -> prints configurations with >= 5 plane rows
"""
import sys
from fractions import Fraction as F
from math import gcd
import gmpy2


def issq(q):
    if q < 0:
        return False
    return gmpy2.is_square(q.numerator) and gmpy2.is_square(q.denominator)


def sqrt(q):
    return F(int(gmpy2.isqrt(q.numerator)), int(gmpy2.isqrt(q.denominator)))


def rats(H, pos=False):
    out = set()
    for q in range(1, H + 1):
        for p in range(-H, H + 1):
            if p == 0 or gcd(p, q) != 1 or (pos and p < 0):
                continue
            out.add(F(p, q))
    return sorted(out)


def plane23(c1, c2, s1, s2):
    if s1 == 0 or s2 == 0 or s1 * s1 == s2 * s2:
        return []
    A2 = (c1 * s1 * s1 - c2 * s2 * s2) / (s2 * s2 - s1 * s1)
    if not issq(A2) or not issq(c1 + A2):
        return []
    A = sqrt(A2)
    B = s1 * sqrt(c1 + A2)
    return [(A, B), (A, -B)] if B != 0 else [(A, B)]


def plane1(c1, c2, d, u):
    s1, s2 = 1 + d * d, u * u + d * d / (u * u)
    K1 = c1 * (1 - d * d) ** 2 / 4
    K2 = c2 * (u * u - d * d / (u * u)) ** 2 / 4
    if s1 == s2:
        return []
    kap = (K1 - K2) / (s1 - s2)
    R = K1 - s1 * kap
    disc = R * R - 4 * d * d * kap * kap
    if not issq(disc):
        return []
    rows = []
    for z in ((R + sqrt(disc)) / 2, (R - sqrt(disc)) / 2):
        if issq(z) and z != 0:
            B = sqrt(z)
            A = kap / B
            rows.append((A, B))
    return rows


def main(H, idx, nproc):
    ds = rats(H)
    us = rats(H)
    ms = rats(H, pos=True)
    c1s = [1, -1, 2, -2, 3, -3, 5, -5, 6, -6, 7, -7, 10, -10, 11, -11, 13, -13, 14, -14, 15, -15, 21, -21]
    n = 0
    for di, d in enumerate(ds):
        if di % nproc != idx or d * d == 1:
            continue
        for u in us:
            if u * u in (1, d, -d, d * d) or u * u * u * u == d * d:
                continue
            s1, s2 = 1 + d, u + d / u
            t1, t2 = 1 - d, u - d / u
            if s1 == 0 or s2 == 0 or t1 == 0 or t2 == 0 or s1 * s1 == s2 * s2 or t1 * t1 == t2 * t2:
                continue
            for c1 in c1s:
                c1 = F(c1)
                for m in ms:
                    A = (c1 - m * m) / (2 * m)
                    c2 = (c1 * s1 * s1 - A * A * (s2 * s2 - s1 * s1)) / (s2 * s2)
                    if c2 == 0:
                        continue
                    r3 = plane23(c1, c2, t1, t2)
                    r1 = plane1(c1, c2, d, u)
                    tot = 2 + len(r3) + len(r1)
                    if tot >= 5:
                        n += 1
                        print(f"CFG rows={tot} p1={len(r1)} p3={len(r3)} d={d} u={u} c1={c1} c2={c2}", flush=True)
    print("done", idx, n, flush=True)


if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
