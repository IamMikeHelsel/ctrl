"""General Klein-four configurations: V = <s: x -> a/x, t: x -> (x - a)/(x - 1)> (p = 1 normal form).

Column j = c_j * prod (x - r) over the V-orbit {u_j, a/u_j, t(u_j), t(a/u_j)} (rational).
The three pairing planes are shared by both columns.  In plane k (basis e1 = P_1k, e2 = Q_1k):
G1(A,B) = -4AB, G2(A,B) = mu nu (from column 2's pairing); rows <-> rational roots (A:B) of
G1/c1 - G2/c2 = 0 with c1/G1(A0,B0) a square.  c2 is fixed by forcing the row
(c1 Q_10 - P_10)/2 (mu = 1) in plane 0.
usage: vsearch2.py Ha Hu Hc idx nproc   (prints CFG lines with >= 6 plane rows)
"""
import sys
from fractions import Fraction as F
from math import gcd
import gmpy2


def issq(q):
    return q >= 0 and gmpy2.is_square(q.numerator) and gmpy2.is_square(q.denominator)


def sqrtq(q):
    return F(int(gmpy2.isqrt(q.numerator)), int(gmpy2.isqrt(q.denominator)))


def rats(H, pos=False):
    out = set()
    for q in range(1, H + 1):
        for p in range(-H, H + 1):
            if p == 0 or gcd(p, q) != 1 or (pos and p < 0):
                continue
            out.add(F(p, q))
    return sorted(out)


def quad(r, s):
    return (F(1), -(r + s), r * s)


def orbit(a, u):
    if u in (0, 1) or u == a:
        return None
    t = lambda z: (z - a) / (z - 1) if z != 1 else None
    r0, r1 = u, a / u
    if r1 == 1:
        return None
    r2, r3 = t(r0), t(r1)
    if r2 is None or r3 is None:
        return None
    pts = [r0, r1, r2, r3]
    if len(set(pts)) < 4:
        return None
    return pts


PAIR = [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]


def coords(v, e1, e2):
    """v = x e1 + y e2 (exact, consistent)."""
    for i, j in ((0, 1), (0, 2), (1, 2)):
        det = e1[i] * e2[j] - e1[j] * e2[i]
        if det != 0:
            x = (v[i] * e2[j] - v[j] * e2[i]) / det
            y = (e1[i] * v[j] - e1[j] * v[i]) / det
            return x, y
    return None


def plane_rows(o1, o2, k, c1, c2):
    (i, j), (m, n) = PAIR[k]
    e1, e2 = quad(o1[i], o1[j]), quad(o1[m], o1[n])
    P2, Q2 = quad(o2[i], o2[j]), quad(o2[m], o2[n])
    cp, cq = coords(P2, e1, e2), coords(Q2, e1, e2)
    if cp is None or cq is None:
        return None
    p1, p2 = cp
    q1, q2 = cq
    det = -p1 * q2 + p2 * q1
    if det == 0:
        return None
    # mu = 2(A q2 - B q1)/det, nu = 2(A p2 - B p1)/det ; G2 = mu nu
    # G2 = 4/det^2 * (q2 p2 A^2 - (q2 p1 + q1 p2) A B + q1 p1 B^2)
    g = 4 / (det * det)
    a2, ab, b2 = g * q2 * p2, -g * (q2 * p1 + q1 * p2), g * q1 * p1
    # H = G1/c1 - G2/c2 = (-4/c1) AB - (a2 A^2 + ab AB + b2 B^2)/c2
    hA2, hAB, hB2 = -a2 / c2, -4 / c1 - ab / c2, -b2 / c2
    rows = []
    sols = []
    if hA2 == 0 and hAB == 0 and hB2 == 0:
        return None
    if hA2 == 0:
        sols.append((F(1), F(0)))
        if hAB != 0:
            sols.append((-hB2 / hAB, F(1)))
    else:
        disc = hAB * hAB - 4 * hA2 * hB2
        if not issq(disc):
            return []
        r = sqrtq(disc)
        for sg in (1, -1):
            sols.append(((-hAB + sg * r) / (2 * hA2), F(1)))
    for A0, B0 in sols:
        G1 = -4 * A0 * B0
        if G1 == 0:
            continue
        l2 = c1 / G1
        if issq(l2):
            l = sqrtq(l2)
            rows.append(tuple(l * (A0 * e1[t] + B0 * e2[t]) for t in range(3)))
    return list(dict.fromkeys(rows))


def plane_form(o, k, v):
    """mu*nu for column orbit o, pairing k, at quadratic v (v in plane k)."""
    (i, j), (m, n) = PAIR[k]
    P, Q = quad(o[i], o[j]), quad(o[m], o[n])
    xy = coords(v, P, Q)
    if xy is None:
        return None
    # v = (nu Q - mu P)/2  ->  mu = -2x, nu = 2y
    return -4 * xy[0] * xy[1]


def cross(u, v):
    return (u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0])


def generic_rows(o1, o2, c1, c2):
    rows = []
    planes = []
    for k in range(3):
        (i, j), (m, n) = PAIR[k]
        planes.append((quad(o1[i], o1[j]), quad(o1[m], o1[n])))
    for k in range(3):
        for kk in range(3):
            if k == kk:
                continue
            nk, nkk = cross(*planes[k]), cross(*planes[kk])
            aL = cross(nk, nkk)
            if aL == (0, 0, 0):
                continue
            N1, N2 = plane_form(o1, k, aL), plane_form(o2, kk, aL)
            if not N1 or not N2:
                continue
            if N1 / N2 == c1 / c2 and issq(c1 / N1):
                l = sqrtq(c1 / N1)
                rows.append(tuple(l * t for t in aL))
    return rows


def main(Ha, Hu, Hc, idx, nproc):
    As = [a for a in rats(Ha) if a != 1 and not issq(a)]
    us = rats(Hu)
    cs = rats(Hc)
    n = 0
    for ai, a in enumerate(As):
        if ai % nproc != idx:
            continue
        orbs = {}
        for u in us:
            o = orbit(a, u)
            if o:
                orbs[frozenset(o)] = o
        ol = list(orbs.values())
        for x1 in range(len(ol)):
            for x2 in range(len(ol)):
                if x1 == x2:
                    continue
                o1, o2 = ol[x1], ol[x2]
                (i, j), (m, nn) = PAIR[0]
                P10, Q10 = quad(o1[i], o1[j]), quad(o1[m], o1[nn])
                for c1 in cs:
                    astar = tuple((c1 * Q10[t] - P10[t]) / 2 for t in range(3))
                    # c2 = mu nu for column 2's plane-0 pairing at astar
                    P2, Q2 = quad(o2[i], o2[j]), quad(o2[m], o2[nn])
                    cp, cq = coords(P2, P10, Q10), coords(Q2, P10, Q10)
                    if cp is None or cq is None:
                        continue
                    xy = coords(astar, P10, Q10)
                    p1, p2 = cp
                    q1, q2 = cq
                    det = -p1 * q2 + p2 * q1
                    if det == 0:
                        continue
                    A, B = xy
                    mu = 2 * (A * q2 - B * q1) / det
                    nu = 2 * (A * p2 - B * p1) / det
                    c2 = mu * nu
                    if c2 == 0:
                        continue
                    tot = 0
                    bad = False
                    for k in range(3):
                        r = plane_rows(o1, o2, k, c1, c2)
                        if r is None:
                            bad = True
                            break
                        tot += len(r)
                    if not bad and tot >= 6:
                        tot += len(generic_rows(o1, o2, c1, c2))
                    if not bad and tot >= int(__import__("os").environ.get("MINROWS", "6")):
                        n += 1
                        print(f"CFG rows={tot} a={a} o1={[str(z) for z in o1]} o2={[str(z) for z in o2]} c1={c1} c2={c2}", flush=True)
    print("done", idx, n, flush=True)


if __name__ == "__main__":
    main(*map(int, sys.argv[1:6]))
