#!/usr/bin/env python3
"""Frozen three-law comparison. Polynomial forcing, exact rational reference.

Numerical evidence only: sample passes are not interval proofs. All paths are
relative to this file. Run with system Python (NumPy and SciPy).
"""
from fractions import Fraction as F
from pathlib import Path
from functools import lru_cache
import csv
import hashlib
import json
import math
import sys
import numpy as np
import scipy
from scipy.linalg import expm

HERE = Path(__file__).resolve().parent
DT = F(1, 2000)
FIELDS = ['q', 'qv', 'qa', 'j', 'snap', 'x', 'v', 'a', 'u', 'ustar',
          'uprime', 'actual_jerk', 'ex', 'ev', 'ea']


def derivative(p):
    return [i*p[i] for i in range(1, len(p))] or [F(0)]


def evaluate(p, t):
    return sum(c*t**i for i, c in enumerate(p))


def reference():
    phases = []
    state = [F(0), F(0), F(0), F(10)]
    t = F(0)

    def add(name, duration, p):
        nonlocal t, state
        derivatives = [p]
        for _ in range(4):
            derivatives.append(derivative(derivatives[-1]))
        assert [evaluate(poly, F(0)) for poly in derivatives[:4]] == state
        phases.append(dict(name=name, start=t, end=t+duration, polys=derivatives))
        state = [evaluate(poly, duration) for poly in derivatives[:4]]
        t += duration

    for name, duration, snap in [
            ('old_plan', F(1, 4), F(0)), ('latency', F(1, 200), F(0)),
            ('jerk_reversal', F(1, 20), F(-400)),
            ('negative_jerk_hold', F(97, 400), F(0)),
            ('jerk_to_zero', F(1, 40), F(400))]:
        add(name, duration, [state[0], state[1], state[2]/2, state[3]/6, snap/24])
    assert state == [F(8782613, 38400000), F(75089, 96000), F(0), F(0)]
    add('cruise', F(3744927, 30035600), [state[0], state[1]])
    V, L = state[1], F(7, 10)
    add('brake', L, [state[0], V, F(0), F(0), -F(5, 2)*V/L**3,
                     3*V/L**4, -V/L**5])
    assert state == [F(3, 5), F(0), F(0), F(0)]
    assert t == F(10491307, 7508900)
    add('hold', F(3, 2)-t, [F(3, 5)])
    return phases


def matrix(law, k, jpoly):
    # State is [ex, ev/10, ea/100, (u-qa)/100] (last omitted for direct).
    n = 3 if law == 'direct' else 4
    A = np.zeros((n+4, n+4))
    A[0, 1] = A[1, 2] = 10
    if n == 3:
        A[2, :3] = [-640, -480, -120]
        jerk_factor = float((80*k-1)/100)
    else:
        A[2, 2:4] = [-80, 80]
        A[3, :4] = [-160, -120, -10, -20]
        for i, c in enumerate(jpoly):
            A[3, n+i] = float((20*k-1)*c/100)
        jerk_factor = -0.01
    # r*w / 100, w=1/100.
    A[2, n] = 0.008
    for i, c in enumerate(jpoly):
        A[2, n+i] += jerk_factor*float(c)
    for i in range(1, 4):
        A[n+i, n+i-1] = i
    return A, n


def output(law, k, y, polys, tau):
    q, qv, qa, j, snap = [evaluate([float(c) for c in p], tau) for p in polys]
    ex, ev, ea = y[0], 10*y[1], 100*y[2]
    ustar = qa-800*ex-60*ev-ea/2+float(k)*j
    u = ustar if law == 'direct' else qa+100*y[3]
    x, v, a = q+ex, qv+ev, qa+ea
    actual_jerk = 80*(u+0.01-a)
    uprime = (1.5*j-800*ev-60*ea-0.5*actual_jerk+float(k)*snap
              if law == 'direct' else 20*(ustar-u))
    return dict(zip(FIELDS, [q, qv, qa, j, snap, x, v, a, u, ustar,
                             uprime, actual_jerk, ex, ev, ea]))


def run(law, k, phases):
    n = 3 if law == 'direct' else 4
    y = np.zeros(n)
    rows, joins = [], []
    old_end = None
    for index, phase in enumerate(phases):
        start, end = phase['start'], phase['end']
        times = sorted({start, end} | {
            i*DT for i in range(math.ceil(start/DT), math.floor(end/DT)+1)})
        A, _ = matrix(law, k, phase['polys'][3])
        augmented = np.r_[y, 1., 0., 0., 0.]
        propagators = {}
        prev = start
        for i, t in enumerate(times):
            delta = t-prev
            if delta:
                if delta not in propagators:
                    propagators[delta] = expm(A*float(delta))
                augmented = propagators[delta] @ augmented
            out = output(law, k, augmented, phase['polys'], float(t-start))
            side = 'start' if i == 0 else ('end' if i == len(times)-1 else 'grid')
            rows.append(dict(t_exact=str(t), t=float(t), phase=index,
                             phase_name=phase['name'], side=side, **out))
            if i == 0 and old_end is not None:
                continuous = ['q', 'qv', 'qa', 'j', 'x', 'v', 'a', 'u', 'ustar']
                differences = {f: out[f]-old_end[f] for f in continuous}
                assert max(abs(v) for v in differences.values()) < 2e-11
                joins.append(dict(t=str(t), differences=differences))
            prev = t
        y = augmented[:n].copy()
        old_end = out
    initial_expected = F(137, 15) if law == 'direct' else F(4, 5)
    assert abs(rows[0]['actual_jerk']-float(initial_expected)) < 1e-12
    filename = law+'.csv'
    with (HERE/filename).open('w') as file:
        writer = csv.DictWriter(file, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    peaks = {}
    for f in ['ex', 'actual_jerk', 'u', 'ustar', 'uprime']:
        row = max(rows, key=lambda r: abs(r[f]))
        peaks[f] = {'max_abs': abs(row[f]), 'signed_value': row[f],
                    'time': row['t_exact'], 'side': row['side']}
    tv = sum(abs(b['u']-a['u']) for a, b in zip(rows, rows[1:]))
    travel = sum(abs(b['x']-a['x']) for a, b in zip(rows, rows[1:]))
    integral_uprime = sum((b['t']-a['t'])*(abs(a['uprime'])+abs(b['uprime']))/2
                         for a, b in zip(rows, rows[1:]))
    return {'law': law, 'feedforward_k': str(k), 'trace': filename,
            'samples': len(rows), 'peaks': peaks, 'endpoint': rows[-1],
            'initial': rows[0], 'min_x': min(r['x'] for r in rows),
            'max_x': max(r['x'] for r in rows),
            'sampled_travel': travel, 'sampled_command_total_variation': tv,
            'trapezoid_integral_abs_uprime': integral_uprime,
            'sampled_internal_position_pass': bool(peaks['ex']['max_abs'] <= .0002),
            'endpoint_position_pass': bool(abs(rows[-1]['x']-.6) <= .0002),
            'continuity_checks': joins}


def main():
    phases = reference()
    serial = [{'name': p['name'], 'start': str(p['start']), 'end': str(p['end']),
               'position_coefficients_local_time': [str(c) for c in p['polys'][0]]}
              for p in phases]
    (HERE/'reference.json').write_text(json.dumps(serial, indent=2)+'\n')
    results = [run(law, k, phases) for law, k in [
        ('direct', F(5, 480)), ('filtered_original', F(5, 480)),
        ('filtered_compensated', F(29, 480))]]
    summary = {'status': 'numerical evidence; independent check pending',
               'plant': "x'=v, v'=a, a'=80(u+0.01-a)",
               'filter': "u'=20(ustar-u), retained from u(0)=0",
               'command': 'ustar=qa-800(x-q)-60(v-qv)-(a-qa)/2+k*j',
               'method': 'SciPy Pade matrix exponential on scaled error state and local polynomial forcing; exact rational reference coefficients and event times',
               'grid_step': str(DT), 'python': sys.version,
               'numpy': np.__version__, 'scipy': scipy.__version__,
               'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               'scope': 'No physical stop or actual corridor acceptance. Sampled passes are not between-sample proofs. Command total variation and travel are grid approximations.',
               'cases': results}
    (HERE/'result.json').write_text(json.dumps(summary, indent=2)+'\n')
    print(json.dumps([{k: r[k] for k in ['law', 'samples', 'peaks',
           'sampled_internal_position_pass', 'endpoint_position_pass',
           'sampled_command_total_variation']} for r in results], indent=2))


if __name__ == '__main__':
    main()
