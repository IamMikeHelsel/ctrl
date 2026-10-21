"""For each low-degree extension of a 1-parameter 4x4 family, analyse y^2 = c*F(x):
rational points (hyperellratpoints), Jacobian rank, and pairwise genus of combined conditions.
usage: lowdeg.py FAMILY "subs" box
"""
import sys
from itertools import combinations, product
from families import pari, load
import famext
from famext import gp_addP, gp_mulP, gp_halfP, gp_sqfree


def new_rows(U, V, box=1, maxdeg=4, torsion=True):
    out = []
    n = len(V)
    for T in combinations(range(n), 3):
        vs = [V[i] for i in T]
        oth = [i for i in range(n) if i not in T]
        a2 = vs[0] + vs[1] + vs[2]
        a4 = vs[0] * vs[1] + vs[0] * vs[2] + vs[1] * vs[2]
        H = [gp_halfP(u, pari(vs)) for u in U]
        TORS = [None] + ([pari([-v, 0]) for v in vs] if torsion else [])
        seen = set()
        for co in product(range(-box, box + 1), repeat=len(U)):
            nz = [c for c in co if c]
            if len(nz) < 2 or nz[0] < 0:
                continue
            P = pari("[0]")
            for c, h in zip(co, H):
                if c:
                    P = gp_addP(a2, a4, P, gp_mulP(a2, a4, h, c))
            if len(P) == 1:
                continue
            for ti, Tp in enumerate(TORS):
                P1 = gp_addP(a2, a4, P, Tp) if Tp is not None else P
                if len(P1) == 1:
                    continue
                R = gp_addP(a2, a4, P1, P1)
                if len(R) == 1:
                    continue
                X = R[0]
                if str(X) in seen or any(X == u for u in U):
                    continue
                seen.add(str(X))
                conds = [gp_sqfree(X + V[i]) for i in oth]
                if all(int(pari.poldegree(F)) <= maxdeg for c0, F in conds):
                    out.append(dict(T=T, co=co, tors=ti, X=X, conds=conds))
    return out


def analyse_quartic(c0, F, H=10**4):
    g = c0 * F
    pts = pari.hyperellratpoints(g, H)
    info = dict(deg=int(pari.poldegree(F)), npts=len(pts))
    if int(pari.poldegree(F)) in (3, 4) and len(pts):
        try:
            E = pari.ellinit(pari.ellfromeqn(pari(f"y^2-({g})")))
            r = pari.ellrank(E)
            info["rank"] = (int(r[0]), int(r[1]))
        except Exception as e:
            info["rank"] = repr(e)[:60]
    info["pts"] = [str(p) for p in pts[:8]]
    return info


if __name__ == "__main__":
    fam = sys.argv[1]
    subs = dict(kv.split("=") for kv in sys.argv[2].split(","))
    box = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    U, V = load(fam, subs)
    for orient, (A, B) in (("row", (U, V)), ("col", (V, U))):
        L = new_rows(A, B, box)
        print(f"== {fam} {subs} {orient}: {len(L)} low-degree extensions")
        allF = []
        for d in L:
            for c0, F in d["conds"]:
                info = analyse_quartic(c0, F)
                print(f"  T={d['T']} co={d['co']} c0={c0} F={F}  {info}")
                allF.append((d, c0, F))
        # pairwise: two new elements whose conditions combine with small extra genus
        for (d1, c1, F1), (d2, c2, F2) in combinations(allF, 2):
            g = pari.gcd(F1, F2)
            if int(pari.poldegree(g)) >= 1:
                print(f"  SHARED roots: {d1['T']}{d1['co']} & {d2['T']}{d2['co']}: gcd={g}")
