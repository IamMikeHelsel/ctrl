#!/usr/bin/env python3
"""Exact-integer verifier for Erdős #939 (r=5 and general r).

Usage:
  uv run --with sympy python verify.py            # verifies the built-in known solutions
  uv run --with sympy python verify.py r A B C ... # verifies: sum of listed summands is r-full etc.

Checks (all with sympy.factorint, no floats):
  * every summand is positive and r-powerful (p | n  =>  p^r | n)
  * summands are pairwise distinct
  * joint gcd of the summands is 1 (Finset.Coprime in the FC file = setwise gcd = 1)
  * the sum is r-powerful
Prints full factorisations.
"""
import sys
from math import gcd
from functools import reduce
from sympy import factorint

def is_full(n, r):
    if n <= 0:
        return False
    return all(e >= r for e in factorint(n).values())

def fstr(n):
    f = factorint(n)
    return " * ".join(f"{p}^{e}" if e > 1 else f"{p}" for p, e in sorted(f.items()))

def check(r, S):
    S = [int(s) for s in S]
    ok = True
    print(f"r = {r}, summands = {S}")
    if len(S) != r - 2:
        print(f"  WARNING: {len(S)} summands, problem wants r-2 = {r-2}")
    if len(set(S)) != len(S):
        print("  FAIL: summands not distinct"); ok = False
    for s in S:
        full = is_full(s, r)
        print(f"  {s} = {fstr(s)}   {r}-full: {full}")
        ok &= full and s > 0
    g = reduce(gcd, S)
    print(f"  joint gcd = {g}")
    ok &= (g == 1)
    D = sum(S)
    fullD = is_full(D, r)
    print(f"  sum = {D} = {fstr(D)}   {r}-full: {fullD}")
    ok &= fullD
    print("  RESULT:", "VALID" if ok else "INVALID")
    return ok

KNOWN = [
    (5, [2**8 * 3**10 * 5**7, 2**12 * 23**6, 11**5 * 13**5]),     # Cambie
    (5, [2**5 * 17**6, 7**11, 2**5 * 3**6 * 7**8]),                # Kitamura
]

if __name__ == "__main__":
    if len(sys.argv) > 1:
        r = int(sys.argv[1]); S = sys.argv[2:]
        sys.exit(0 if check(r, S) else 1)
    allok = True
    for r, S in KNOWN:
        allok &= check(r, S)
    sys.exit(0 if allok else 1)
