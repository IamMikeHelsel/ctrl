#!/usr/bin/env python3
"""Numerical solve of the iota-antisymmetric degree-10 system (see hyperosc10.py for the setup)."""
import sys, random, pickle
from sympy import symbols, lambdify, Poly, cancel, Matrix, S, expand, together, nsimplify, factor
import mpmath as mp
exec(open('hyperosc10.py').read().split("P_(\"computing sections ...\")")[0])   # reuse definitions
P_("computing sections ...")
SP = S_section('P', 1, b); S2 = S_section('2P', 1, c); SPb = S_section('P', 1, c)
def oddpart(C):
    Vv = C - iota_pull(C); return Matrix([cancel(Vv[i]) for i in odd_idx])
V1 = oddpart(SP); V2 = oddpart(S2); V3 = oddpart(SPb)
P_("odd parts done")
mp.mp.dps = 30
def run(Va, Vb, tag, nstarts=2500):
    Mx = Matrix.hstack(Va, Vb)
    minors = []
    for i in range(4):
        for j in range(i+1, 4):
            m = cancel(Mx[i,0]*Mx[j,1] - Mx[j,0]*Mx[i,1])
            if m != 0: minors.append(m.as_numer_denom()[0])
    P_(f"[{tag}] minors: {len(minors)}")
    fs = [lambdify((d, b, c), m, 'mpmath') for m in minors]
    Jac = [[lambdify((d, b, c), m.diff(v), 'mpmath') for v in (d, b, c)] for m in minors]
    fa = [lambdify((d,b,c), e, 'mpmath') for e in Va]; fb = [lambdify((d,b,c), e, 'mpmath') for e in Vb]
    sols = []
    random.seed(1)
    for trial in range(nstarts):
        z = mp.matrix([mp.mpc(random.uniform(-3,3), random.uniform(-3,3)) for _ in range(3)])
        ok = False
        for it in range(60):
            F = mp.matrix([f(*z) for f in fs])
            J = mp.matrix([[Jac[i][k](*z) for k in range(3)] for i in range(len(fs))])
            try:
                dz = mp.lu_solve(J.H*J, J.H*F)   # Gauss-Newton
            except ZeroDivisionError:
                break
            z = z - dz
            if mp.norm(dz) < mp.mpf(10)**(-25):
                ok = True; break
        if not ok: continue
        res = max(abs(f(*z)) for f in fs)
        if res > mp.mpf(10)**(-15): continue
        na = max(abs(f(*z)) for f in fa); nb = max(abs(f(*z)) for f in fb)
        dd, bb, cc = z
        # degenerate: V vanishes, or d in {0, roots of disc: d^2-11d-1=0}
        deg = (na < 1e-10) or (nb < 1e-10) or abs(dd) < 1e-10 or abs(dd**2 - 11*dd - 1) < 1e-10
        key = (mp.nstr(dd, 12), mp.nstr(bb, 12), mp.nstr(cc, 12))
        if key in [s_[0] for s_ in sols]: continue
        sols.append((key, deg, na, nb))
        P_(f"[{tag}] sol d={mp.nstr(dd,15)} b={mp.nstr(bb,15)} c={mp.nstr(cc,15)} degenerate={deg} |V1|={mp.nstr(na,3)} |V2|={mp.nstr(nb,3)}")
        if not deg:
            if abs(dd.imag) < 1e-20:
                P_("      d real; minpoly (deg<=4):", mp.findpoly(dd.real, 6, maxcoeff=10**9), " b:", mp.findpoly(bb.real, 6, maxcoeff=10**9) if abs(bb.imag)<1e-20 else "complex", " c:", mp.findpoly(cc.real, 6, maxcoeff=10**9) if abs(cc.imag)<1e-20 else "complex")
            else:
                # integer relation among powers of complex d: combine real & imag parts with a generic weight
                w = mp.mpf('0.7310585786300049')
                vec = [ (dd**k).real + w*(dd**k).imag for k in range(7) ]
                rel = mp.pslq(vec, maxcoeff=10**6, maxsteps=10**5)
                P_("      d complex; integer relation on powers 0..6:", rel)
    P_(f"[{tag}] total distinct solutions: {len(sols)}, nondegenerate: {sum(1 for s_ in sols if not s_[1])}")
run(V1, V2, "P vs 2P")
run(V1, V3, "P vs P")
