"""Independent exact check of the K_{3,6} hit and its transposed K_{5,4} form."""

from math import isqrt, lcm

Ns = [349102656, 1034586000, 4883112000]
ds = [6720, 15855, 26880, 45440, 69510, 129290]


def D(n: int) -> set[int]:
    out, a = set(), 1
    while a * a <= n:
        if n % a == 0:
            out.add(n // a - a)
        a += 1
    return out


common = set.intersection(*(D(n) for n in Ns))
print("full common difference set:", sorted(common))
assert set(ds) <= common

# Grid: rows {0} ∪ {4N}, columns {d²}. Transpose and normalise by the smallest new row.
rows = [0] + [4 * n for n in Ns]
cols = [d * d for d in ds]
assert all(isqrt(u + v) ** 2 == u + v for u in rows for v in cols)
new_rows = sorted(cols)
v0 = new_rows[0]
Ns2 = [v - v0 for v in new_rows[1:]]
ds2 = [isqrt(u + v0) for u in rows]
k = 1
if any(x % 4 for x in Ns2):
    k = 4
Ns2 = [x * k // 4 for x in Ns2]
ds2 = [d * isqrt(k) for d in ds2]
print("transposed: N =", Ns2)
print("            d =", ds2)
assert all(isqrt(4 * n + d * d) ** 2 == 4 * n + d * d for n in Ns2 for d in ds2)
print("5 N's share", len(set(ds2)), "differences: OK")
