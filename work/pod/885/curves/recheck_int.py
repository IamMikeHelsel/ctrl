"""Independent integer re-check: full divisor enumeration of D(N) via sympy factorisation.
usage: python recheck_int.py "N1,N2,..." "d1,d2,..."
"""
import sys
from sympy import divisors, factorint

Ns = [int(x) for x in sys.argv[1].split(",")]
ds = [int(x) for x in sys.argv[2].split(",")]
assert len(set(Ns)) == len(Ns) and len(set(ds)) == len(ds)
sets = []
for N in Ns:
    Dn = {}
    for a in divisors(N):
        b = N // a
        if a <= b:
            Dn[b - a] = (a, b)
    sets.append(Dn)
    print(f"N={N} = {factorint(N)}  |D(N)|={len(Dn)}")
    for d in ds:
        a, b = Dn[d]
        assert a * b == N and b - a == d
        print(f"   d={d}: {a} * {b}")
common = set.intersection(*[set(s) for s in sets])
print("common differences:", sorted(common))
assert set(ds) <= common
print(f"OK: {len(Ns)} numbers share {len(common)} common factor differences")
