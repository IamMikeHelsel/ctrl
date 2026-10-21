"""Two-parameter deformation of Lagrange's polynomial 7x7 configuration:
C1 -> C1 + t1*w1^2, C2 -> C2 + t2*w2^2 (w1 = 2x^2+6x+7, w2 = 4x^2+10x+1), row a1 and column 0 fixed.
Utilities: solve at (t1,t2); exact square-class data (P, Q) of the leading coefficients of rows 0,2,3.
"""
from deform2 import solve, Z0, pari, polys
from obstr import R, C

msq = pari("msq")
X = pari("x")
W1 = pari("2*x^2+6*x+7")
W2 = pari("4*x^2+10*x+1")
A1 = msq(R[1])


def fixed_for(t1, t2):
    C1 = C[1] + pari(t1) * W1 ** 2
    C2 = C[2] + pari(t2) * W2 ** 2
    f = {("C", 1, k): pari.polcoef(C1, k) for k in range(5)}
    f.update({("C", 2, k): pari.polcoef(C2, k) for k in range(5)})
    f.update({("a", 1, k): pari.polcoef(A1, k) for k in range(3)})
    return f


def at(t1, t2, z=None):
    z, res, it = solve(fixed_for(t1, t2), z=z, its=60)
    return z, res


def PQ(z, i):
    al = z[("a", i, 2)]
    p = pari.algdep(al, 4)
    p = p / pari.pollead(p)
    return pari.polcoef(p, 2), pari.polcoef(p, 0), p
