"""Numerical continuation of the full 7x7 Lagrange polynomial pattern: is the 2-dim first-order
deformation space (mod GL2) unobstructed?  Gauss-Newton from z0 + eps*k back to F=0, then compare
GL2-invariants (j-invariants of the column quartics) with the Lagrange values.
"""
import json, sys
import numpy as np
from famext import pari

msq = pari("msq")
d = json.load(open("poly77_lagrange.json"))
R = [pari(r) for r in d["R"]]
C = [pari(c) for c in d["C"]]
ZERO = 3
inc = sorted((i, j) for i in range(7) for j in range(7) if pari.issquare(R[i] + C[j]))


def cf(p, n):
    return [float(pari.polcoef(p, k, "x")) for k in range(n)]


A0 = [cf(msq(r), 3) for r in R]
C0 = [cf(c, 5) for c in C]
B0 = {e: cf(msq(R[e[0]] + C[e[1]]), 3) if R[e[0]] + C[e[1]] != 0 else [0.0] * 3 for e in inc}
cols = [j for j in range(7) if j != ZERO]


def pack(A, Cc, Bb):
    return np.array(sum(A, []) + sum([Cc[j] for j in cols], []) + sum([Bb[e] for e in inc], []))


def unpack(z):
    A = [z[3 * i:3 * i + 3] for i in range(7)]
    o = 21
    Cc = {ZERO: np.zeros(5)}
    for j in cols:
        Cc[j] = z[o:o + 5]
        o += 5
    Bb = {}
    for e in inc:
        Bb[e] = z[o:o + 3]
        o += 3
    return A, Cc, Bb


def F(z):
    A, Cc, Bb = unpack(z)
    out = []
    for (i, j) in inc:
        out.append(np.convolve(A[i], A[i]) + Cc[j] - np.convolve(Bb[(i, j)], Bb[(i, j)]))
    return np.concatenate(out)


def J(z, h=1e-7):
    f0 = F(z)
    M = np.zeros((len(f0), len(z)))
    for k in range(len(z)):
        dz = np.zeros(len(z)); dz[k] = h
        M[:, k] = (F(z + dz) - F(z - dz)) / (2 * h)
    return M


def jinv(c):
    # binary quartic c0 + c1 x + ... + c4 x^4 ; a=c4,b=c3/4... use I,J
    e, dd, cc, b, a = c  # a x^4 + b x^3 + cc x^2 + dd x + e
    I = 12 * a * e - 3 * b * dd + cc * cc
    Jv = 72 * a * cc * e + 9 * b * cc * dd - 27 * a * dd * dd - 27 * e * b * b - 2 * cc ** 3
    return I ** 3 / (4 * I ** 3 - Jv ** 2)


def invariants(z):
    A, Cc, Bb = unpack(z)
    return [jinv(Cc[j]) for j in cols]


z0 = pack(A0, C0, B0)
print("residual at z0", np.abs(F(z0)).max())
M = J(z0)
U_, S, Vt = np.linalg.svd(M)
print("smallest singular values", S[-10:])
null = Vt[np.sum(S > 1e-6 * S[0]):]
print("kernel dim", len(null))
inv0 = np.array(invariants(z0))
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
scale = np.abs(z0).max()
for eps in [1e-3, 1e-2, 3e-2, 1e-1]:
    for trial in range(3):
        k = null.T @ rng.standard_normal(len(null))
        z = z0 + eps * scale * k / np.linalg.norm(k)
        r0 = np.abs(F(z)).max()
        for it in range(60):
            f = F(z)
            if np.abs(f).max() < 1e-9 * scale ** 2:
                break
            Mz = J(z)
            dz = np.linalg.lstsq(Mz, -f, rcond=None)[0]
            z = z + dz
        res = np.abs(F(z)).max()
        dinv = np.abs(np.array(invariants(z)) - inv0).max()
        print(f"eps {eps:g} trial {trial}: start res {r0:.2e} -> {res:.2e} after {it} its; max |dj| = {dinv:.3e}", flush=True)
        np.save(f"logs/deform_eps{eps}_t{trial}.npy", z)
