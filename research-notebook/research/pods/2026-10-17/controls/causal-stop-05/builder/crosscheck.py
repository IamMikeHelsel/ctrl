#!/usr/bin/env python3
"""Second numerical method: physical coordinates, 80-digit Taylor exponential.

This was prepared by the same coordinator as compare.py. It is a numerical
cross-check, not a substitute for the separately assigned independent grader.
"""
from pathlib import Path
from fractions import Fraction as F
import csv
import json
import time
import mpmath as mp

HERE = Path(__file__).resolve().parent
mp.mp.dps = 80


def number(value):
    f = F(value)
    return mp.mpf(f.numerator)/f.denominator


def poly_value(coefficients, t, order=0):
    answer = mp.mpf(0)
    for i in range(order, len(coefficients)):
        answer += number(coefficients[i])*mp.factorial(i)/mp.factorial(i-order)*t**(i-order)
    return answer


def system(law, k):
    n = 3 if law == 'direct' else 4
    # Physical x, v/10, a/100, u/100; then q and its six derivatives; then 1.
    A = mp.matrix(n+8)
    A[0, 1] = A[1, 2] = 10
    for i in range(6):
        A[n+i, n+i+1] = 1
    A[2, n+7] = number('1/125')
    if n == 3:
        for i, value in enumerate([-640, -480, -120]):
            A[2, i] = value
        for i, value in enumerate([640, 48, number('6/5'), number('4/5')*k]):
            A[2, n+i] = value
    else:
        A[2, 2], A[2, 3] = -80, 80
        for i, value in enumerate([-160, -120, -10, -20]):
            A[3, i] = value
        for i, value in enumerate([160, 12, number('3/10'), k/5]):
            A[3, n+i] = value
    return A, n


def main():
    began = time.monotonic()
    source = json.loads((HERE/'result.json').read_text())
    reference = json.loads((HERE/'reference.json').read_text())
    fields = ['q', 'qv', 'qa', 'j', 'snap', 'x', 'v', 'a', 'u', 'ustar',
              'uprime', 'actual_jerk', 'ex', 'ev', 'ea']
    reports = []
    for case in source['cases']:
        law, k = case['law'], number(case['feedforward_k'])
        A, n = system(law, k)
        actual = mp.matrix(n, 1)
        with (HERE/case['trace']).open() as f:
            rows = list(csv.DictReader(f))
        maxima = {f: mp.mpf(0) for f in fields}
        peak_errors = mp.mpf(0)
        row_count = 0
        propagators = {}
        for index, phase in enumerate(reference):
            coefficients = phase['position_coefficients_local_time']
            y = mp.matrix(list(actual)+[poly_value(coefficients, mp.mpf(0), i)
                                       for i in range(7)]+[mp.mpf(1)])
            prev = F(phase['start'])
            for row in (r for r in rows if int(r['phase']) == index):
                t = F(row['t_exact'])
                delta = t-prev
                if delta:
                    if delta not in propagators:
                        propagators[delta] = mp.expm(A*number(delta), method='taylor')
                    y = propagators[delta]*y
                q, qv, qa, j, snap = [y[n+i] for i in range(5)]
                x, v, a = y[0], 10*y[1], 100*y[2]
                ex, ev, ea = x-q, v-qv, a-qa
                ustar = qa-800*ex-60*ev-ea/2+k*j
                u = ustar if n == 3 else 100*y[3]
                jerk = 80*(u+number('1/100')-a)
                up = (number('3/2')*j-800*ev-60*ea-jerk/2+k*snap
                      if n == 3 else 20*(ustar-u))
                values = [q, qv, qa, j, snap, x, v, a, u, ustar, up, jerk, ex, ev, ea]
                for field, value in zip(fields, values):
                    maxima[field] = max(maxima[field], abs(mp.mpf(row[field])-value))
                peak_errors = max(peak_errors, abs(ex))
                prev = t
                row_count += 1
            actual = mp.matrix([y[i] for i in range(n)])
        assert row_count == case['samples']
        assert bool(peak_errors <= number('1/5000')) == case['sampled_internal_position_pass']
        assert max(maxima.values()) < mp.mpf('3e-10')
        reports.append({'law': law, 'rows': row_count,
                        'max_absolute_column_difference': {k: mp.nstr(v, 25) for k, v in maxima.items()},
                        'max_sampled_position_error': mp.nstr(peak_errors, 65),
                        'endpoint_x_v_a': [mp.nstr(actual[i]*10**i, 65) for i in range(3)]})
    result = {'passed': True, 'decimal_digits': 80, 'mpmath_version': mp.__version__,
              'method': 'Physical-state augmented reference derivatives; mpmath Taylor matrix exponential. All trace rows checked; no SciPy segment state reused.',
              'independence': 'Different coordinates and exponential method, same coordinator author. Independent human/agent review still required.',
              'absolute_tolerance_in_each_column_unit': '3e-10',
              'seconds': time.monotonic()-began, 'cases': reports}
    (HERE/'high-precision-check.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
