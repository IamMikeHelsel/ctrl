"""Rational points on the full rationality locus of the deformed Lagrange 7x7 configuration.

a = (5k^2-16k-25)/(k^2+5)  (189-5a^2 = square),  b = 3(l^2-8l+21)/(l^2-21)  (21b^2-45 = square);
remaining: (ab)^2 - 81 = square and 25a^2 + 441b^2 - 1890 = square.  (Lagrange: a=5, b=3.)
k=p/q, l=r/s, heights <= H; numpy QR sieve mod small primes, exact gmpy2 check.
usage: ssearch2.py H nproc idx
"""
import sys
from math import gcd
import numpy as np
import gmpy2

PR = [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67]


def pts(H, f):
    out = set()
    for q in range(1, H + 1):
        for p in range(-H, H + 1):
            if gcd(p, q) != 1:
                continue
            n, d = f(p, q)
            if d == 0:
                continue
            g = gcd(n, d)
            n, d = n // g, d // g
            if d < 0:
                n, d = -n, -d
            out.add((abs(n), d))
    return sorted(out)


def main(H, nproc, idx):
    A = pts(H, lambda p, q: (5 * p * p - 16 * p * q - 25 * q * q, p * p + 5 * q * q))
    B = pts(H, lambda r, s: (3 * (r * r - 8 * r * s + 21 * s * s), r * r - 21 * s * s))
    print("points on conics:", len(A), len(B), flush=True)
    An = np.array([x for x, _ in A], dtype=object)
    Ad = np.array([y for _, y in A], dtype=object)
    qr = {m: np.zeros(m, dtype=bool) for m in PR}
    for m in PR:
        for x in range(m):
            qr[m][x * x % m] = True
    Am = {m: (np.array([x % m for x, _ in A], dtype=np.int64), np.array([y % m for _, y in A], dtype=np.int64)) for m in PR}
    hits = 0
    for j, (bn, bd) in enumerate(B):
        if j % nproc != idx:
            continue
        mask = np.ones(len(A), dtype=bool)
        for m in PR:
            an, ad = Am[m]
            bnm, bdm = bn % m, bd % m
            v3 = ((an * bnm) ** 2 - 81 * (ad * bdm) ** 2) % m
            v4 = (25 * an * an * bdm * bdm + 441 * bnm * bnm * ad * ad - 1890 * ad * ad * bdm * bdm) % m
            mask &= qr[m][v3] & qr[m][v4]
        for i in np.nonzero(mask)[0]:
            an, ad = A[i]
            if an * bn == 9 * ad * bd:
                continue
            v3 = (an * bn) ** 2 - 81 * (ad * bd) ** 2
            v4 = 25 * an * an * bd * bd + 441 * bn * bn * ad * ad - 1890 * ad * ad * bd * bd
            if v3 >= 0 and v4 >= 0 and gmpy2.is_square(v3) and gmpy2.is_square(v4):
                hits += 1
                print(f"HIT a={an}/{ad} b={bn}/{bd}", flush=True)
    print("done", idx, "hits", hits, flush=True)


if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
