"""Shioda heights on the K3 elliptic surface E_B: Y^2 = (X+C1)(X+C2)(X+C3) over Q(x), C_i quartics.

h(R) = 4 + 2 (R.O) - sum_v contr_v(R)   (chi = 2).  Fibres: I_{2n} where exactly one C_i-C_j
vanishes (order n), I0* where all three do (order 1).  Pairing <P,Q> = (h(P+Q)-h(P)-h(Q))/2.
x = c + 1/t first, so that x = infinity becomes the finite fibre t = 0 and t = infinity is good.
"""
from fractions import Fraction as Fr
from itertools import combinations
from famext import pari, gp_addP, gp_halfP, gp_negP

C0 = 97  # x = C0 + 1/t; must not be a root of any C_i - C_j


def wt(f, w):
    """weight-w form: t^w f(C0 + 1/t) (a polynomial in t when deg f <= w)."""
    g = pari.subst(pari(f), "x", pari(f"{C0}+1/t")) * pari(f"t^{w}")
    return pari.subst(g, "t", pari("x"))


class K3:
    def __init__(self, C):
        self.C = [wt(c, 4) for c in C]
        self.a2 = sum(self.C)
        self.a4 = self.C[0] * self.C[1] + self.C[0] * self.C[2] + self.C[1] * self.C[2]
        self.fib = {}
        for i, j in combinations(range(3), 2):
            d = self.C[i] - self.C[j]
            assert pari.poldegree(d) == 4, "fibre at infinity is bad; change C0"
            fa = pari.factor(d)
            for k in range(len(fa[0])):
                f = fa[0][k]
                if pari.poldegree(f) > 0:
                    self.fib.setdefault(str(f), [f, {}])[1][(i, j)] = int(fa[1][k])
        self.types = {}
        for key, (f, o) in self.fib.items():
            if len(o) == 1:
                (pr, n), = o.items()
                self.types[key] = ("I", 2 * n, pr)
            elif len(o) == 3 and all(v == 1 for v in o.values()):
                self.types[key] = ("I0*", 0, None)
            else:
                raise ValueError(f"fibre {key} orders {o}")

    def half(self, X):
        return gp_halfP(wt(X, 4), pari(self.C))

    def add(self, P, Q):
        return gp_addP(self.a2, self.a4, P, Q)

    def height(self, R):
        if len(R) == 1:
            return Fr(0)
        x = R[0]
        num, den = pari.numerator(x), pari.denominator(x)
        ok, q = pari.issquare(den, 1) if False else (True, None)
        dden = int(pari.poldegree(den))
        assert dden % 2 == 0
        RO = dden // 2
        ex = int(pari.poldegree(num)) - dden - 4
        if ex > 0:
            RO += (ex + 1) // 2
        h = Fr(4 + 2 * RO)
        for key, (f, o) in self.fib.items():
            if pari.polresultant(den, f) == 0:      # R meets O at this fibre
                continue
            typ, m, pr = self.types[key]
            d = int(pari.poldegree(f))
            if typ == "I":
                n = m // 2
                i = pr[0]
                g = num + self.C[i] * den
                k = 0
                while k < n and pari.Mod(g, f ** (k + 1)) == 0:
                    k += 1
                h -= Fr(d * k * (m - k), m)
            else:
                g = num + self.C[0] * den
                if pari.Mod(g, f) == 0:
                    h -= d
        return h

    def gram(self, Ps):
        hs = [self.height(P) for P in Ps]
        n = len(Ps)
        G = [[Fr(0)] * n for _ in range(n)]
        for i in range(n):
            G[i][i] = hs[i]
            for j in range(i + 1, n):
                G[i][j] = G[j][i] = (self.height(self.add(Ps[i], Ps[j])) - hs[i] - hs[j]) / 2
        return G
