"""Direction 2 (Picard-jump locus): V-configurations with C1 - C2 = lam * q_k^2, q_k a fixed-point
quadratic of V (two I2 fibres merge into I4, twice).  c2/c1 is then forced by the orbits.
Prints CFG lines (vsearch2 format) with >= MINROWS plane+generic rows, for vcheck/polyrows.
usage: vdeg.py Ha Hu Hc idx nproc
"""
import os
import sys
from fractions import Fraction as F
from vsearch2 import rats, issq, orbit, plane_rows, generic_rows


def mono(o):
    p = [F(1)]
    for r in o:
        p = [a - r * b for a, b in zip(p + [F(0)], [F(0)] + p)]
    return p  # coefficients x^4..x^0


def sqr(q):
    a, b, c = q
    return [a * a, 2 * a * b, b * b + 2 * a * c, 2 * b * c, c * c]


def main(Ha, Hu, Hc, idx, nproc):
    minrows = int(os.environ.get("MINROWS", "5"))
    As = [a for a in rats(Ha) if a != 1 and not issq(a)]
    us, cs = rats(Hu), rats(Hc)
    n = 0
    for ai, a in enumerate(As):
        if ai % nproc != idx:
            continue
        qs = [(F(1), F(0), -a), (F(1), F(-2), a), (F(1), -2 * a, a)]
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
                m1, m2 = mono(o1), mono(o2)
                for qk in qs:
                    s = sqr(qk)
                    # m1 - rho m2 - lam s = 0 : solve from x^4 and x^0, check rest
                    # x^4: 1 - rho - lam = 0 ; x^3: m1[1] - rho m2[1] - lam s[1] = 0
                    det = -m2[1] + s[1]
                    if det == 0:
                        continue
                    rho = (m1[1] - s[1]) / (m2[1] - s[1])
                    lam = 1 - rho
                    if rho == 0 or lam == 0:
                        continue
                    if any(m1[t] - rho * m2[t] - lam * s[t] != 0 for t in range(5)):
                        continue
                    for c1 in cs:
                        c2 = c1 * rho
                        tot, bad = 0, False
                        for k in range(3):
                            r = plane_rows(o1, o2, k, c1, c2)
                            if r is None:
                                bad = True
                                break
                            tot += len(r)
                        if bad:
                            continue
                        tot += len(generic_rows(o1, o2, c1, c2))
                        if tot >= minrows:
                            n += 1
                            print(f"CFG rows={tot} a={a} o1={[str(z) for z in o1]} o2={[str(z) for z in o2]} c1={c1} c2={c2}", flush=True)
    print("done", idx, n, flush=True)


if __name__ == "__main__":
    main(*map(int, sys.argv[1:6]))
