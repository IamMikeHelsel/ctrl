"""Parametric 4x4 families (Lagrange/Guy; Choudhry arXiv:2508.07806 Thms 3, 4) as PARI polynomials."""
import cypari2

pari = cypari2.Pari()
pari.allocatemem(4 * 10**9)

FAM = {}

FAM["lagrange"] = ("u,v", [
    "9*(18*u^2+50*u*v+37*v^2)^2", "36*(u^2+13*u*v+16*v^2)^2",
    "36*(9*u^2+53*u*v+64*v^2)^2", "4*(3*u^2-25*u*v-48*v^2)^2"], [
    "0", "20*(u-4*v)*(11*u+19*v)*(u+4*v)*(u+v)",
    "36*(3*u+11*v)*(7*u+12*v)*(3*u+4*v)*(u+v)", "756*(u-v)*(3*u+2*v)*(u+3*v)*(u+2*v)"])

_A0 = "(v1^4-6*v1^2*v2^2+v2^4)"
_S = "(v1^2+v2^2)"
FAM["chou3"] = ("u1,u2,v1,v2", [
    f"{_A0}^2*(v1^2-v2^2)^2*(u1^2+u2^2)^2",
    f"{_A0}^2*{_S}^2*(u1^2-u2^2)^2",
    f"(v1^2-v2^2)^2*({_S}^2*u1^2-16*u1*u2*v1^2*v2^2-{_S}^2*u2^2)^2",
    f"(v1^2-v2^2)^2*({_S}^2*u1^2+16*u1*u2*v1^2*v2^2-{_S}^2*u2^2)^2"], [
    "0",
    f"{_A0}^2*((v2-v1)*u1+(v1+v2)*u2)*((v1+v2)*u1+(v1-v2)*u2)*((v1-v2)*u1+(v1+v2)*u2)*((v1+v2)*u1-(v1-v2)*u2)",
    f"-(v1^2-v2^2)^2*({_S}*u1+4*u1*v1*v2-{_S}*u2)*({_S}*u1-4*u1*v1*v2-{_S}*u2)*({_S}*u1+4*u2*v1*v2+{_S}*u2)*({_S}*u1-4*u2*v1*v2+{_S}*u2)",
    f"-(v1^2-v2^2)^2*({_S}*u1+4*u1*v1*v2+{_S}*u2)*({_S}*u1-4*u1*v1*v2+{_S}*u2)*({_S}*u1+4*u2*v1*v2-{_S}*u2)*({_S}*u1-4*u2*v1*v2-{_S}*u2)"])

FAM["chou4a"] = ("m,q,r", [
    "16*m^2*(m^4-1)^2*((5*m^4-2*m^2+1)*q^2-2*(m^4-6*m^2+1)*q*r+(m^4-2*m^2+5)*r^2)^2",
    "16*m^2*(m^4-1)^2*((5*m^4-2*m^2+1)*q^2-(m^4-2*m^2+5)*r^2)^2",
    "16*m^2*(m^4-1)^2*((7*m^4-2*m^2-1)*q^2-(2*m^4-12*m^2+2)*q*r-(m^4+2*m^2-7)*r^2)^2",
    "(m^2-1)^2*((3*m^8+40*m^6-26*m^4-1)*q^2+2*(m^4-6*m^2+1)^2*q*r-(m^8+26*m^4-40*m^2-3)*r^2)^2"], [
    "0",
    "-4*m^2*((m^4+6*m^2-3)*q+(m^4-2*m^2+5)*r)*((3*m^4-6*m^2-1)*q-(m^4-2*m^2+5)*r)*((5*m^4-2*m^2+1)*q-(3*m^4-6*m^2-1)*r)*((5*m^4-2*m^2+1)*q+(m^4+6*m^2-3)*r)",
    "-128*m^2*(m^4-1)^3*(q^2-r^2)*(3*m^2*q-m^2*r-q+3*r)*(m^2*q+r)",
    "16*(m^2+1)^2*(m^2-1)^3*(m^2*q^2-r^2)*((m^4+6*m^3-2*m-1)*q-(m^4+2*m^3-6*m-1)*r)*((m^4-6*m^3+2*m-1)*q-(m^4-2*m^3+6*m-1)*r)"])

FAM["chou4b"] = ("m,q,r", [
    "16*m^2*(m^4-1)^2*((m^6-2*m^4+5*m^2)*q^2+(2*m^5-12*m^3+2*m)*q*r+(5*m^4-2*m^2+1)*r^2)^2",
    "16*m^2*(m^4-1)^2*((m^6-2*m^4+5*m^2)*q^2-(5*m^4-2*m^2+1)*r^2)^2",
    "(m^2-1)^2*((m^10+26*m^6-40*m^4-3*m^2)*q^2+(2*m^9-24*m^7+76*m^5-24*m^3+2*m)*q*r-(3*m^8+40*m^6-26*m^4-1)*r^2)^2",
    "16*m^2*(m^4-1)^2*((m^6+2*m^4-7*m^2)*q^2-(2*m^5-12*m^3+2*m)*q*r-(7*m^4-2*m^2-1)*r^2)^2"], [
    "0",
    "-4*m^2*((m^5+6*m^3-3*m)*q-(5*m^4-2*m^2+1)*r)*((3*m^5-6*m^3-m)*q+(5*m^4-2*m^2+1)*r)*((m^5-2*m^3+5*m)*q+(3*m^4-6*m^2-1)*r)*((m^5-2*m^3+5*m)*q-(m^4+6*m^2-3)*r)",
    "-16*m^2*(m^2+1)^2*(m^2-1)^3*(q^2-r^2)*((m^5-2*m^4+6*m^2-m)*q+(m^4-6*m^3+2*m-1)*r)*((m^5+2*m^4-6*m^2-m)*q+(m^4+6*m^3-2*m-1)*r)",
    "128*m^3*(m^4-1)^3*(m*r-q)*(m^2*q^2-r^2)*((m^3-3*m)*q+(3*m^2-1)*r)"])


def load(name, subs):
    """subs: dict var -> value (pari-able string). Returns (U, V) lists of pari objects."""
    vars_, U, V = FAM[name]
    out = []
    for lst in (U, V):
        res = []
        for e in lst:
            g = pari(e)
            for k, val in subs.items():
                g = pari.subst(g, k, pari(val))
            res.append(g)
        out.append(res)
    return out


def check_symbolic(name):
    vars_, U, V = FAM[name]
    bad = []
    for i, a in enumerate(U):
        for j, b in enumerate(V):
            if not pari.issquare(pari(f"({a})+({b})")):
                bad.append((i, j))
    return bad


if __name__ == "__main__":
    for k in FAM:
        print(k, "non-square entries:", check_symbolic(k))
