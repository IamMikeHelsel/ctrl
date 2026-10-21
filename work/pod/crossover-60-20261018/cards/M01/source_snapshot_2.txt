"""Try to extend the 6x4 grid to 6x5 (which settles Erdős 885 at k=5).

Integer form: Ns (5 numbers) share ds (4 differences). A new column of the rational grid is a
rational w = p/q with 4N + w^2 a rational square for all N in Ns, i.e. p is a factor difference
of q^2 N for every N. For each q we enumerate D(q^2 N_min) exactly from its factorisation, so
each q is checked exhaustively. Usage: python3 extend_6x4.py QMAX [QMIN]
"""

import sys
from math import gcd, isqrt

Ns = [206222625, 677376000, 2019635200, 4786481700, 16670745700]
ds = [13440, 75936, 129360, 279840]


def factor(n: int) -> dict[int, int]:
    f, p = {}, 2
    while p * p <= n:
        while n % p == 0:
            f[p] = f.get(p, 0) + 1
            n //= p
        p += 1 if p == 2 else 2
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def divisors(f: dict[int, int]) -> list[int]:
    out = [1]
    for p, e in f.items():
        out = [d * p**k for d in out for k in range(e + 1)]
    return out


def main() -> None:
    qmax = int(sys.argv[1])
    qmin = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    base = min(Ns, key=lambda n: len(divisors(factor(n))))
    others = [n for n in Ns if n != base]
    fb = factor(base)
    hits = 0
    for q in range(qmin, qmax + 1):
        fq = factor(q)
        f = dict(fb)
        for p, e in fq.items():
            f[p] = f.get(p, 0) + 2 * e
        M = base * q * q
        known = {q * d for d in ds}
        for a in divisors(f):
            b = M // a
            if a >= b:
                continue
            p = b - a
            if p in known or gcd(p, q) != 1 and q > 1 and all(p % r == 0 for r in fq):
                continue
            if all(isqrt(4 * n * q * q + p * p) ** 2 == 4 * n * q * q + p * p for n in others):
                print(f"HIT q={q} p={p} w={p}/{q}", flush=True)
                hits += 1
        if q % 1000 == 0:
            print(f"progress q={q} hits={hits}", flush=True)
    print(f"done q<={qmax} hits={hits}")


if __name__ == "__main__":
    main()
