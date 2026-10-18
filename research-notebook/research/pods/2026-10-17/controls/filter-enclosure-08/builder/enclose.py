#!/usr/bin/env python3
"""Directed rational Taylor enclosures for two frozen filter witnesses.

No floating-point arithmetic, external numeric package, or imported simulator.
This is a validated numerical calculation, not a Lean proof of ODE semantics.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import time

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parents[1] / 'causal-stop-05' / 'builder' / 'reference.json'
SCALE = 10**600
TAIL_TARGET = Q(1, 10**500)


def ceilq(q):
    return -((-q.numerator) // q.denominator)


def point(q):
    q = Q(q) * SCALE
    return (q.numerator // q.denominator, ceilq(q))


def add(a, b):
    return (a[0]+b[0], a[1]+b[1])


def mul(q, a):
    q = Q(q)
    lo, hi = (a if q >= 0 else (a[1], a[0]))
    return (q.numerator*lo // q.denominator,
            -((-q.numerator*hi) // q.denominator))


def derivative(p):
    return [i*p[i] for i in range(1, len(p))] or [Q(0)]


def matrix(k, jerk):
    # Error state [ex, ev/10, ea/100, (u-qa)/100], then [1,t,t²,t³].
    A = [[Q(0) for _ in range(8)] for _ in range(8)]
    A[0][1] = A[1][2] = Q(10)
    A[2][2], A[2][3], A[2][4] = Q(-80), Q(80), Q(1, 125)
    A[3][:4] = [Q(-160), Q(-120), Q(-10), Q(-20)]
    for i, c in enumerate(jerk):
        A[2][4+i] -= c/100
        A[3][4+i] = (20*k-1)*c/100
    for i in range(1, 4):
        A[4+i][3+i] = Q(i)
    return A


def exp_enclosure(A, dt, initial):
    """Enclose exp(dt*A)*v for every v in the supplied closed interval box.

    If a=||dt*A||∞ and B bounds ||v||∞, the omitted series after term n is
    bounded by B*a^(n+1)/(n+1)!/(1-a/(n+2)) when a/(n+2)<1.
    Every finite-series arithmetic operation rounds outwards in exact integers.
    """
    M = [[dt*c for c in row] for row in A]
    a = max(sum(abs(c) for c in row) for row in M)
    B = Q(max(max(abs(lo), abs(hi)) for lo, hi in initial), SCALE)
    total, term, norm_term = list(initial), list(initial), Q(1)
    for n in range(1, 4097):
        term = [mul(Q(1, n), tuple(map(sum, zip(*(mul(c, x) for c, x in zip(row, term))))))
                for row in M]
        total = [add(s, v) for s, v in zip(total, term)]
        norm_term *= a/n
        if a < n+2:
            tail = B*norm_term*a/(n+1)/(1-a/(n+2))
            if tail <= TAIL_TARGET:
                pad = ceilq(tail*SCALE)
                enclosed = [(lo-pad, hi+pad) for lo, hi in total]
                return enclosed, {'terms': n+1, 'last_degree': n,
                                  'matrix_infinity_norm_times_dt': str(a),
                                  'initial_norm_bound': str(B),
                                  'tail_bound_upper': str(Q(pad, SCALE)),
                                  'tail_grid_units': str(pad)}
    raise RuntimeError('Taylor degree cap reached; no enclosure was accepted')


def coarse(a, digits=15):
    grid = 10**digits
    lower = Q(a[0]*grid // SCALE, grid)
    upper = Q(-((-a[1]*grid) // SCALE), grid)
    return {'lower': str(lower), 'upper': str(upper),
            'width': str(upper-lower)}


def run(name, k, witness, phases):
    state = [point(0)]*4
    records = []
    reached = Q(0)
    for phase in phases:
        start, end = Q(phase['start']), Q(phase['end'])
        if start >= witness:
            break
        assert start == reached
        dt = min(witness, end)-start
        p = [Q(c) for c in phase['position_coefficients_local_time']]
        j = derivative(derivative(derivative(p)))
        A = matrix(k, j)
        initial = state+[point(1), point(0), point(0), point(0)]
        enclosure, evidence = exp_enclosure(A, dt, initial)
        state = enclosure[:4]
        reached = start+dt
        records.append({'phase': phase['name'], 'start': str(start), 'dt': str(dt),
                        'matrix': [[str(c) for c in row] for row in A],
                        'initial_grid_intervals': [[str(a),str(b)] for a,b in initial],
                        'end_grid_intervals': [[str(a),str(b)] for a,b in enclosure],
                        **evidence})
    assert reached == witness
    result = coarse(state[0])
    assert Q(result['lower']) > Q(1, 5000)
    return {'law': name, 'k': str(k), 'witness_time': str(witness),
            'position_error_enclosure_m': result,
            'positive_violation_margin_m': str(Q(result['lower'])-Q(1,5000)),
            'phases': records}


def main():
    started = time.monotonic()
    raw = SOURCE.read_bytes()
    phases = json.loads(raw)
    cases = [run('filtered_original', Q(5,480), Q(171,400), phases),
             run('filtered_compensated', Q(29,480), Q(1581,2000), phases)]
    # Outward rounding must hold for signs, negative endpoints and zero.
    for q in [Q(-7,3), Q(0), Q(4,7)]:
        for lo, hi in [(-9,2),(1,8),(-8,-1)]:
            actual = sorted([q*lo,q*hi])
            got = mul(q,(lo,hi))
            assert got[0] <= actual[0] <= actual[1] <= got[1]
    result = {'status':'two rational Taylor enclosures exclude the position target',
              'method':'outward integer interval arithmetic plus an explicit geometric Taylor-tail bound',
              'scale_decimal_digits':600, 'tail_target':str(TAIL_TARGET),
              'reference_sha256':hashlib.sha256(raw).hexdigest(),
              'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'scope':'Classical constant-coefficient phase ODE interpreted via its matrix exponential. General exponential remainder argument is documented, not formalized in Lean here. Independent review pending.',
              'cases':cases}
    (HERE/'enclosure.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'seconds':time.monotonic()-started,
                      'cases':[{k:c[k] for k in ['law','witness_time','position_error_enclosure_m',
                                                'positive_violation_margin_m']} for c in cases]},indent=2))


if __name__ == '__main__':
    main()
