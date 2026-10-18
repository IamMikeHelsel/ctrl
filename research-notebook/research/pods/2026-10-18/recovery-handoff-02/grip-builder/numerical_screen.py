"""High-precision illustrative looseness screen. Not a verified trajectory bound.

The simple bound is rational arithmetic. Decimal bisection evaluates the exact
constant worst-envelope trajectory; it is numerical evidence, not Lean proof.
All output remains in this grip-builder folder.
"""
from decimal import Decimal as D, localcontext
from fractions import Fraction as F
from pathlib import Path
import json

CASES = [
    ("old-exact-contract", "0.001", "0.41", "0.1", "0.05", "1.2", "8"),
    ("smaller-true-initial-speed", "0", "0.4", "0.1", "0.05", "1.2", "8"),
    ("longer-loss", "0", "0.4", "0.1", "0.2", "1.2", "8"),
    ("slower-recovered-response", "0", "0.4", "0.1", "0.05", "1.2", "2"),
    ("near-rest", "0", "0.01", "0", "0", "1", "8"),
    ("already-stationary", "0", "0", "0", "0", "1", "8"),
]


def dec(q):
    return D(q.numerator) / D(q.denominator)


def run():
    rows = []
    with localcontext() as ctx:
        ctx.prec = 70
        for name, Xs, vs, As, Ts, bs, ls in CASES:
            X, v, A, T, b, lam = map(F, (Xs, vs, As, Ts, bs, ls))
            P = v*T+A*T*T/2
            U = v+A*T
            C = (A+b)/lam
            V = U+C
            bound = P+V*V/(2*b)
            deadline = T+V/b
            dd = {k: dec(q) for k, q in zip(("P", "U", "C", "V", "T", "b", "lambda"), (P, U, C, V, T, b, lam))}

            def velocity(s):
                return dd["U"]-dd["b"]*s+dd["C"]*(1-(-dd["lambda"]*s).exp())

            def position(s):
                return dd["P"]+dd["V"]*s-dd["b"]*s*s/2-dd["C"]/dd["lambda"]*(1-(-dd["lambda"]*s).exp())

            if v == 0:
                stop, travel = D(0), D(0)
            else:
                lo, hi = D(0), dec(V/b)
                assert velocity(lo) > 0 and velocity(hi) < 0
                for _ in range(220):
                    mid = (lo+hi)/2
                    if velocity(mid) > 0:
                        lo = mid
                    else:
                        hi = mid
                stop, travel = dd["T"]+(lo+hi)/2, position((lo+hi)/2)
            rows.append({
                "name": name,
                "inputs": dict(zip(("x0_upper_m", "v0_upper_m_per_s", "A_m_per_s2", "T_s", "b_m_per_s2", "lambda_per_s"), (Xs, vs, As, Ts, bs, ls))),
                "simple_forward_displacement_bound_m": {"exact": str(bound), "decimal": str(dec(bound))},
                "simple_reference_position_bound_m": {"exact": str(X+bound), "decimal": str(dec(X+bound))},
                "simple_deadline_s": {"exact": str(deadline), "decimal": str(dec(deadline))},
                "numeric_first_zero_s": str(stop),
                "numeric_forward_travel_m": str(travel),
                "numeric_peak_reference_position_m": str(dec(X)+travel),
                "numeric_distance_excess_m": str(dec(bound)-travel),
                "numeric_bound_to_travel_ratio": str(dec(bound)/travel) if travel else None,
            })
            if name == "old-exact-contract":
                assert X+bound == F("0.1605859375")
    output = {"status": "Illustrative numerical envelope evaluation, not a Lean certificate or measured plant result", "model": "a=A,q=A on [0,T); q=-b,r=lambda after T; shared physical state", "rows": rows}
    Path(__file__).with_name("numerical-screen.json").write_text(json.dumps(output, indent=2)+"\n")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    run()
