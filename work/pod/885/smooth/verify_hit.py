#!/usr/bin/env python3
"""Exact certificate checker for a reported K_{a,b}.

Usage: python verify_hit.py N1,N2,... d1,d2,...
"""
import math
import sys


def divisor_differences(n: int) -> set[int]:
    out: set[int] = set()
    for a in range(1, math.isqrt(n) + 1):
        if n % a == 0:
            b = n // a
            if a < b:
                out.add(b - a)
    return out


def main() -> None:
    if len(sys.argv) == 1:
        ns = [349102656, 1034586000, 4883112000]
        ds = [6720, 15855, 26880, 45440, 69510, 129290]
    elif len(sys.argv) == 3:
        ns = [int(x) for x in sys.argv[1].split(",")]
        ds = [int(x) for x in sys.argv[2].split(",")]
    else:
        raise SystemExit("usage: verify_hit.py N1,N2,... d1,d2,...")
    assert len(ns) == len(set(ns)) and all(n > 0 for n in ns)
    assert len(ds) == len(set(ds)) and all(d >= 1 for d in ds)
    for n in ns:
        actual = divisor_differences(n)
        for d in ds:
            assert d in actual, (n, d, "missing from divisor enumeration")
            s = math.isqrt(4 * n + d * d)
            assert s * s == 4 * n + d * d, (n, d, "not a square")
            assert (s - d) % 2 == 0
            a = (s - d) // 2
            b = (s + d) // 2
            assert a >= 1 and a * b == n and b - a == d
    print(f"PASS: exact K_{{{len(ns)},{len(ds)}}}; "
          f"{len(ns) * len(ds)} edges checked two ways")


if __name__ == "__main__":
    main()
