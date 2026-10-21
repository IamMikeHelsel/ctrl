"""Positive control: n=7. Take the paper's A, its top skew pair, solve the 10-D inner problem; save both A's (40 digits)."""
import json, numpy as np
import mpmath as mp
from bl import *
from barrier import barrier_min_sigma
A7 = np.array([[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[6,-5,-13,0,0,0,0],[-14,-18,0,0,0,0,0],[12,-12,11,0,0,0,0],[0,0,0,-6,0,-14,0],[0,0,0,6,-18,0,0]], float)
sig, K, Y, sv = skew_top_pair(A7)
A0, Ar, resid, rank = affine_family(K, Y / 1.0)   # pair for A7/sig
B0 = BS(A0); Br = np.array([BS(a) for a in Ar])
f, z, t, nit = barrier_min_sigma(B0, Br, tol=1e-12)
Aopt = A0 + np.tensordot(z, Ar, axes=(0, 0))
s, k = norms(Aopt)
print("n=7 inner optimum: f =", f, " sym", s, " skew", k, "gap", k - s)
mp.mp.dps = 50
def dump(A, fn, note):
    json.dump(dict(note=note, n=A.shape[0], A=[[mp.nstr(mp.mpf(float(x)), 40) for x in row] for row in A]), open(fn, 'w'), indent=1)
dump(A7, 'candidates/n7_paper_integer_A.json', 'Kressner-Vandereycken Theorem 2 matrix (positive control)')
dump(Aopt, 'candidates/n7_inner_optimum_A.json', 'n=7 positive control: A in the affine family of the paper pair minimizing the sym norm (double-precision accurate only; NOT mp-refined)')
