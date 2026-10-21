"""Search rational points on the surface S of fully rational deformations of Lagrange's 7x7 pattern.

t1 = 125 - 5a^2, t2 = 21b^2 - 189 (a = p/q, b = r/s), C = 189q^2 - 5p^2.  Conditions:
 (i)   C (21 r^2 - 45 s^2) = square
 (ii)  C (25 p^2 s^2 + 441 r^2 q^2 - 1890 q^2 s^2) = square
 (iii) C (p^2 r^2 - 81 q^2 s^2) = square
Lagrange: (a,b) = (5,3).  Join on squarefree class of C and of 21r^2-45s^2.
usage: ssearch.py H
"""
import sys
from math import gcd
from collections import defaultdict
import gmpy2


def sqf(n):
    """squarefree kernel with sign, by trial division (n moderate)."""
    if n == 0:
        return 0
    s = -1 if n < 0 else 1
    n = abs(n)
    k = 1
    d = 2
    while d * d <= n:
        e = 0
        while n % d == 0:
            n //= d
            e += 1
        if e & 1:
            k *= d
        d += 1 if d == 2 else 2
    return s * k * n


def main(H):
    A = defaultdict(list)
    for q in range(1, H + 1):
        for p in range(1, H + 1):
            if gcd(p, q) != 1:
                continue
            C = 189 * q * q - 5 * p * p
            if C == 0:
                continue
            A[sqf(C)].append((p, q, C))
    print("A classes", len(A), flush=True)
    hits = 0
    for s in range(1, H + 1):
        for r in range(1, H + 1):
            if gcd(r, s) != 1:
                continue
            m = 21 * r * r - 45 * s * s
            if m == 0:
                continue
            k = sqf(m)
            for (p, q, C) in A.get(k, ()):
                v2 = C * (25 * p * p * s * s + 441 * r * r * q * q - 1890 * q * q * s * s)
                if v2 < 0 or not gmpy2.is_square(v2):
                    continue
                v3 = C * (p * p * r * r - 81 * q * q * s * s)
                if v3 < 0 or not gmpy2.is_square(v3):
                    continue
                hits += 1
                print(f"HIT a={p}/{q} b={r}/{s} t1={125 - 5 * p * p / q / q} t2={21 * r * r / s / s - 189}", flush=True)
    print("done hits", hits)


if __name__ == "__main__":
    main(int(sys.argv[1]))
