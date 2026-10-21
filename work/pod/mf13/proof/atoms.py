"""Atomic gauge N4(P) := gauge of conv(ATOMS), ATOMS = { Y'K' : ||Y'||=||K'||=1 skew, and
     (rank K' <= 4)  or  (rank Y' <= 4)  or  (exists T sym. involution anticommuting with both) }.
Every atom has N <= 1 (Lean rank-4 theorem / adjoint / YK=(YT)(TK)), so N <= N4.
Cutting-plane LP:  max <G,P> s.t. <G,a_i> <= 1 (finite atom list) ; value >= N4 always (relaxation), and
the LP dual gives an explicit decomposition P = sum lam_i a_i with sum lam_i = value  (valid certificate of N(P) <= value).
Oracle (heuristic, multi-start BFGS over SO(n)): most violated atom for the current G."""
import numpy as np
from scipy.optimize import minimize, linprog
from scipy.linalg import expm
from core import skew_of, bases

def skew_basis(n):
    B = []
    for i in range(n):
        for j in range(i + 1, n):
            E = np.zeros((n, n)); E[i, j] = 1 / np.sqrt(2); E[j, i] = -1 / np.sqrt(2); B.append(E)
    return np.array(B)

class Atoms:
    def __init__(self, n):
        self.n = n
        self.Kall = skew_basis(n)
        sub = [E for E in self.Kall if np.abs(E[4:, :]).sum() + np.abs(E[:, 4:]).sum() == 0]   # skew(4) block
        self.Ksub = np.array(sub)
        T0 = np.diag([1, 1, 1, -1, -1, -1.0][:n] if n == 6 else [1] * (n // 2 + n % 2) + [-1] * (n // 2))
        self.T0 = T0
        self.Kanti = np.array([E for E in self.Kall if np.abs(T0 @ E + E @ T0).max() < 1e-12])
        # families: (left basis, right basis); atom = Y'K', value <Gt, Y_b K_a>
        self.fam = {'rk4K': (self.Kall, self.Ksub), 'rk4Y': (self.Ksub, self.Kall), 'cT': (self.Kanti, self.Kanti)}
        self.prod = {f: np.einsum('bij,ajk->baik', L, R) for f, (L, R) in self.fam.items()}

    def Q(self, x):
        return expm(skew_of(x, self.n))

    def val(self, f, Gt):
        M = np.einsum('ik,baik->ba', Gt, self.prod[f])
        u, s, vt = np.linalg.svd(M)
        return s[0], u[:, 0], vt[0]

    def atom(self, f, x):
        """return best atom matrix (in original frame) for family f at rotation x, for the current G"""
        Q = self.Q(x); Gt = Q.T @ self.G @ Q
        s, u, v = self.val(f, Gt)
        L, R = self.fam[f]
        Yp = np.tensordot(u, L, 1); Kp = np.tensordot(v, R, 1)
        return s, Q @ Yp @ Kp @ Q.T, (Q @ Yp @ Q.T, Q @ Kp @ Q.T)

    def oracle(self, G, rng, starts=3, warm=()):
        self.G = G; m = self.n * (self.n - 1) // 2
        found = []
        for f in self.fam:
            x0s = [rng.standard_normal(m) * 1.5 for _ in range(starts)] + [w for (ff, w) in warm if ff == f]
            for x0 in x0s:
                obj = lambda x: -self.val(f, self.Q(x).T @ G @ self.Q(x))[0]
                r = minimize(obj, x0, method='L-BFGS-B', options=dict(maxiter=80))
                found.append((-r.fun, f, r.x))
        found.sort(key=lambda t: -t[0])
        out = []
        for s, f, x in found:
            _, a, YK = self.atom(f, x); out.append((s, f, x, a))
        return out

def N4(P, rng=None, iters=60, tol=1e-6, verbose=False, init_atoms=()):
    n = P.shape[0]; At = Atoms(n); rng = rng or np.random.default_rng(0)
    atoms = list(init_atoms); warm = []; info = []
    m = n * (n - 1) // 2
    for t in range(240):
        At.G = P if t % 2 == 0 else rng.standard_normal((n, n))
        f = list(At.fam)[t % 3]
        _, a, _ = At.atom(f, rng.standard_normal(m) * 1.5)
        atoms += [a, -a]
    G = P / np.linalg.norm(P)
    for it in range(iters):
        found = At.oracle(G, rng, warm=warm[-9:])
        s, f = found[0][0], found[0][1]
        for (si, fi, xi, ai) in found:
            if si > 1 + tol:
                atoms.append(ai); atoms.append(-ai); warm.append((fi, xi))
        A = np.array([a.ravel() for a in atoms]) if atoms else np.zeros((0, n * n))
        res = linprog(-P.ravel(), A_ub=A if len(atoms) else None, b_ub=np.ones(len(atoms)) if len(atoms) else None,
                      bounds=[(-50, 50)] * (n * n), method='highs')
        G = res.x.reshape(n, n); ub = -res.fun
        lam = -res.ineqlin.marginals if len(atoms) else np.zeros(0)
        info.append((it, ub, s, f))
        if verbose: print(f"  it {it}: LP ub = {ub:.6f}  oracle max = {s:.6f} [{f}]  #atoms = {len(atoms)}", flush=True)
        if s <= 1 + tol and it > 0: break
    box_active = np.abs(np.abs(G) - 50).min() < 1e-6
    return ub, lam, atoms, box_active, info
