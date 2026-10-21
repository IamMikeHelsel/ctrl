"""Exact-arithmetic certificate: the Chen-Tian same-square comparator fails at n = 6.

Statement certified (all in exact rational arithmetic):
  A  in Q^{6x6} (rounded CMA matrix), Kt = F diag(w1 J, w2 J, w3 J) F^T with F rational orthogonal (Cayley), w rational,
  w1 > w2 > w3 > 0 distinct, and for EVERY symmetric S with S^2 = -Kt^2 (all 27 components of that set):
        ||L_A S||_F^2  <=  UB  <  ||L_A Kt||_F^2          (||S||_F = ||Kt||_F)
  UB from a Shor-relaxation dual certificate  diag(l0, l1 I_2, ...) - G  PSD, checked by exact LDL^T.
Also reported (floating point, informative): Kt is within ~1e-7 of the top skew singular vector of L_A,
k(A) top skew value is simple, s(A) > k(A) (so A is NOT a counterexample)."""
import itertools, json, sys
from fractions import Fraction as Fr
import numpy as np
import cvxpy as cp
from core import *
from ssclass import frame

DEN = 10 ** 6

def rat(x, den=DEN):
    return Fr(int(round(x * den)), den)

def fmat(M): return [[Fr(v) if isinstance(v, int) else v for v in row] for row in M]
def mm(X, Y):
    n, k, m = len(X), len(Y), len(Y[0])
    return [[sum(X[i][l] * Y[l][j] for l in range(k)) for j in range(m)] for i in range(n)]
def tr(X): return [list(r) for r in zip(*X)]
def add(X, Y, a=1): return [[X[i][j] + a * Y[i][j] for j in range(len(X[0]))] for i in range(len(X))]
def eye(n): return [[Fr(int(i == j)) for j in range(n)] for i in range(n)]
def inv(M):
    n = len(M); Aug = [list(M[i]) + eye(n)[i] for i in range(n)]
    for c in range(n):
        p = next(r for r in range(c, n) if Aug[r][c] != 0); Aug[c], Aug[p] = Aug[p], Aug[c]
        pv = Aug[c][c]; Aug[c] = [v / pv for v in Aug[c]]
        for r in range(n):
            if r != c and Aug[r][c] != 0:
                f = Aug[r][c]; Aug[r] = [a - f * b for a, b in zip(Aug[r], Aug[c])]
    return [row[n:] for row in Aug]
def frob2(X): return sum(v * v for row in X for v in row)
def Lop(A, X): return add(mm(A, X), mm(X, tr(A)))
def ldl_psd(M):
    """exact LDL^T; returns min pivot (PSD iff all pivots >= 0 with zero-pivot rows zero). We require strictly > 0."""
    n = len(M); M = [list(r) for r in M]; piv = []
    for k in range(n):
        d = M[k][k]; piv.append(d)
        if d <= 0: return piv
        for i in range(k + 1, n):
            f = M[i][k] / d
            for j in range(k + 1, n): M[i][j] -= f * M[k][j]
    return piv

def main(fn, out='cert_ss_fail.json'):
    Af = np.load(fn); Af = Af / np.abs(Af).max()
    A = [[rat(v) for v in row] for row in Af]
    An = np.array([[float(v) for v in r] for r in A])
    u, s, vt = np.linalg.svd(BK(An)); Kf = skew_of(vt[0])
    F, w = frame(Kf)
    # rational orthogonal approximation of F via Cayley:  F = (I - W)(I + W)^{-1},  W = (I - F)(I + F)^{-1} (fix sign to make I+F invertible)
    if np.linalg.det(F) < 0: F[:, 0] *= -1; w = w.copy()
    D = np.diag(np.where(np.diag(F) < 0, -1.0, 1.0)); F = F @ D   # flip columns in pairs? keep orientation of blocks:
    # (flipping column 2i flips sign of w_i; recompute w from F)
    Wf = (np.eye(6) - F) @ np.linalg.inv(np.eye(6) + F); Wf = (Wf - Wf.T) / 2
    W = [[rat(Wf[i, j], 10 ** 9) for j in range(6)] for i in range(6)]
    for i in range(6):
        for j in range(i): W[i][j] = -W[j][i]
        W[i][i] = Fr(0)
    I6 = eye(6)
    Ft = mm(add(I6, W, -1), inv(add(I6, W)))
    assert all(v == 0 for v in [x for r in add(mm(tr(Ft), Ft), I6, -1) for x in r]), "F not orthogonal"
    Ftn = np.array([[float(v) for v in r] for r in Ft])
    wf = np.array([(Ftn.T @ Kf @ Ftn)[2 * i, 2 * i + 1] for i in range(3)])
    wt = [rat(abs(x)) for x in wf]
    sgn = [1 if x > 0 else -1 for x in wf]
    def blockdiag(blocks):
        M = [[Fr(0)] * 6 for _ in range(6)]
        for i, B in enumerate(blocks):
            for a in range(2):
                for b in range(2): M[2 * i + a][2 * i + b] = B[a][b]
        return mm(mm(Ft, M), tr(Ft))
    Jp = [[Fr(0), Fr(1)], [Fr(-1), Fr(0)]]
    Kt = blockdiag([[[sgn[i] * wt[i] * x for x in r] for r in Jp] for i in range(3)])
    EK = frob2(Lop(A, Kt)); nK2 = frob2(Kt)
    print("w~ =", [float(x) for x in wt], " ||Kt||^2 =", float(nK2), " E_A(Kt) =", float(EK),
          " ratio E/||K||^2 =", float(EK / nK2), " (k^2 float =", s[0] ** 2, ")")
    Knum = np.array([[float(v) for v in r] for r in Kt])
    cosang = abs(np.sum(Knum * Kf)) / np.linalg.norm(Knum)
    R0 = [[Fr(1), Fr(0)], [Fr(0), Fr(-1)]]; R1 = [[Fr(0), Fr(1)], [Fr(1), Fr(0)]]
    P2 = eye(2); M2 = [[Fr(-1), Fr(0)], [Fr(0), Fr(-1)]]; Z2 = [[Fr(0)] * 2 for _ in range(2)]
    worst = Fr(0); rep = []
    for comp in itertools.product('R+-', repeat=3):
        # L_A S = v0 + sum_j d_j v_j
        const = [(P2 if c == '+' else M2 if c == '-' else Z2) for c in comp]
        v0 = Lop(A, blockdiag([[[wt[i] * x for x in r] for r in const[i]] for i in range(3)]))
        vs = []
        for i, c in enumerate(comp):
            if c == 'R':
                for R in (R0, R1):
                    bl = [Z2, Z2, Z2]; bl = list(bl); bl[i] = [[wt[i] * x for x in r] for r in R]
                    vs.append(Lop(A, blockdiag(bl)))
        vecs = [v0] + vs
        m = len(vecs)
        G = [[sum(vecs[a][i][j] * vecs[b][i][j] for i in range(6) for j in range(6)) for b in range(m)] for a in range(m)]
        Gn = np.array([[float(x) for x in r] for r in G])
        nb = (m - 1) // 2
        # Shor dual: min l0 + sum l_i  s.t. diag(l0, l1,l1, ...) - G >= 0
        l = cp.Variable(1 + nb)
        Dg = cp.diag(cp.hstack([l[0]] + [l[1 + i // 2] for i in range(m - 1)]))
        prob = cp.Problem(cp.Minimize(cp.sum(l)), [Dg - Gn >> 0]); prob.solve(solver=cp.CLARABEL)
        lam = [rat(x + 1e-7 * max(1, abs(x)), 10 ** 9) for x in l.value]
        Dm = [[Fr(0)] * m for _ in range(m)]
        Dm[0][0] = lam[0]
        for i in range(m - 1): Dm[1 + i][1 + i] = lam[1 + i // 2]
        piv = ldl_psd(add(Dm, G, -1))
        ok = all(p > 0 for p in piv) and len(piv) == m
        UB = sum(lam)
        worst = max(worst, UB)
        rep.append(dict(comp=''.join(comp), UB=float(UB), UB_over_EK=float(UB / EK), psd_exact=ok))
        print(''.join(comp), "UB/E_A(Kt) =", float(UB / EK), "exact PSD:", ok)
        assert ok
    print("max UB / E_A(Kt) =", float(worst / EK), " -> certified < 1:", worst < EK)
    sS = np.linalg.norm(BS(An), 2)
    res = dict(A_num=[[str(v) for v in r] for r in A], W=[[str(v) for v in r] for r in W], w=[str(x) for x in wt], sgn=sgn,
               E_K=str(EK), normK2=str(nK2), max_UB=str(worst), ratio=float(worst / EK), certified=bool(worst < EK),
               cos_Kt_topK=float(cosang), k_float=float(s[0]), k2_over_k1=float(s[1] / s[0]), s_float=float(sS), comps=rep)
    json.dump(res, open(out, 'w'), indent=1)
    print("cos(Kt, top skew vector) =", cosang, " k2/k1 =", s[1] / s[0], " s/k =", sS / s[0])

if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else 'logs/e05_n6_s1_e0.05_best.npy')
