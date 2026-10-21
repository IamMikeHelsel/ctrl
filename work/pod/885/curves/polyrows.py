"""Complete enumeration of polynomial rows of degree <= 2K for polynomial columns over Q[x].

Row X valid for columns {a} u J iff X + v_a = z^2 and z^2 + delta_j = w_j^2 (delta_j = v_j - v_a),
i.e. w_j - z = c_j D_j, w_j + z = delta_j/(c_j D_j) with D_j a monic divisor of delta_j, so
z = alpha_j/c_j - c_j beta_j, alpha_j = delta_j/(2 D_j), beta_j = D_j/2.
Two columns j,k determine z (kernel computation); further columns are tested directly.
Complete for the stated degree bound (z of degree <= K).
"""
import sys
from itertools import combinations, product
from families import pari, load


def divisors_monic(f):
    fa = pari.factor(f)
    facs = [(fa[0][i], int(fa[1][i])) for i in range(len(fa[0]))]
    facs = [(p, e) for p, e in facs if int(pari.poldegree(p)) > 0]
    out = []
    for es in product(*[range(e + 1) for _, e in facs]):
        D = pari(1)
        for (p, _), k in zip(facs, es):
            D = D * p ** k
        D = D / pari.pollead(D)
        out.append(D)
    return out


def vec(p, K):
    return [pari.polcoef(p, i, "x") for i in range(K + 1)]


def solve_pair(aj, bj, ak, bk, K):
    """All (c_j) giving common z = aj/cj - cj bj = ak/ck - ck bk; returns list of z polys."""
    M = pari.matrix(K + 1, 4, [x for i in range(K + 1) for x in (vec(aj, K)[i], vec(bj, K)[i], vec(ak, K)[i], vec(bk, K)[i])])
    ker = pari.matker(M)
    d = len(ker)
    zs = []
    if d == 1:
        k = [ker[0][i] for i in range(4)]
        if k[0] * k[1] == 0 or k[0] * k[1] != k[2] * k[3]:
            return []
        lam2 = -1 / (k[0] * k[1])
        if not pari.issquare(lam2):
            return []
        lam = pari.sqrtint(pari.numerator(lam2)) / pari.sqrtint(pari.denominator(lam2))
        for s in (1, -1):
            L = s * lam
            cj = 1 / (L * k[0])
            zs.append(aj / cj - cj * bj)
    elif d >= 2:
        # generic param: brute force over the 2-dim family is rare; solve via resultant in c_j, c_k
        cj, ck = pari("cj"), pari("ck")
        eqs = [pari.polcoef(ck * aj - cj * cj * ck * bj - cj * ak + cj * ck * ck * bk, i, "x") for i in range(K + 1)]
        eqs = [e for e in eqs if e != 0]
        if len(eqs) >= 2:
            R = pari.polresultant(eqs[0], eqs[1], ck)
            if R != 0:
                for r in pari.nfroots(None, R) if False else [f[0] for f in [pari.factor(R)]]:
                    pass
            fa = pari.factor(R) if R != 0 else None
            if fa is not None:
                for i in range(len(fa[0])):
                    f = fa[0][i]
                    if int(pari.poldegree(f, "cj")) == 1:
                        root = -pari.polcoef(f, 0, "cj") / pari.polcoef(f, 1, "cj")
                        if root != 0:
                            zs.append(aj / root - root * bj)
    return zs


def in_hyperbola(z, a, b, K):
    """Is z = a/c - c b for some rational c != 0 ?"""
    M = pari.matrix(K + 1, 2, [x for i in range(K + 1) for x in (vec(a, K)[i], vec(b, K)[i])])
    zv = pari.matrix(K + 1, 1, vec(z, K))
    try:
        sol = pari.matinverseimage(M, zv)
    except Exception:
        return False
    if len(sol) == 0:
        return False
    p, q = sol[0][0], sol[0][1] if False else (sol[0, 0], sol[1, 0])
    return p * q == -1


def poly_rows(V, K=2):
    """Return dict X -> set of column indices satisfied (only rows satisfying >= 3 columns)."""
    res = {}
    n = len(V)
    for a in range(n):
        others = [j for j in range(n) if j != a]
        H = {}
        for j in others:
            dlt = V[j] - V[a]
            if dlt == 0:
                continue
            dd = int(pari.poldegree(dlt))
            H[j] = []
            for D in divisors_monic(dlt):
                k = int(pari.poldegree(D))
                if dd - k <= K and k <= K:
                    H[j].append((dlt / (2 * D), D / 2))
        for j, k in combinations(others, 2):
            for (aj, bj) in H.get(j, []):
                for (ak, bk) in H.get(k, []):
                    for z in solve_pair(aj, bj, ak, bk, K):
                        X = z * z - V[a]
                        key = str(X)
                        if key in res:
                            continue
                        sat = {a}
                        for l in range(n):
                            if l != a and pari.issquare(X + V[l]):
                                sat.add(l)
                        res[key] = (X, sat)
    return {k: v for k, v in res.items() if len(v[1]) >= 3}


if __name__ == "__main__":
    fam = sys.argv[1]
    subs = dict(kv.split("=") for kv in sys.argv[2].split(","))
    K = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    U, V = load(fam, subs)
    for orient, (A, B) in (("rows", (U, V)), ("cols", (V, U))):
        R = poly_rows(B, K)
        known = [str(a) for a in A]
        print(f"== {fam} {subs} {orient}: {len(R)} polynomial {orient} (deg<= {2*K}) valid for >=3 of {len(B)}")
        for key, (X, sat) in R.items():
            tag = "KNOWN" if key in known else "new"
            extra = ""
            if len(sat) < len(B):
                from famext import gp_sqfree
                extra = " degF=" + str([int(pari.poldegree(gp_sqfree(X + B[l])[1])) for l in range(len(B)) if l not in sat])
            print(f"  {tag} sat={sorted(sat)}{extra} X={key[:90]}")
