#!/usr/bin/env python3
"""Exact characteristic polynomials and numerical roots; no new plant run."""
from pathlib import Path
import json
import math
import sympy as sp

s = sp.symbols('s')
direct = sp.Matrix([[0, 1, 0], [0, 0, 1], [-64000, -4800, -120]])
filtered = sp.Matrix([[0, 1, 0, 0], [0, 0, 1, 0], [0, 0, -80, 80],
                      [-16000, -1200, -10, -20]])
p = direct.charpoly(s).as_expr()
q = filtered.charpoly(s).as_expr()
assert sp.expand(p-(s+40)**3) == 0
assert q == s**4+100*s**3+2400*s**2+96000*s+1280000
roots = [complex(z) for z in sp.nroots(q, maxsteps=300)]
pair = next(z for z in roots if z.imag > 0)
routh_b = sp.Rational(100*2400-96000, 100)
routh_c = (routh_b*96000-100*1280000)/routh_b
assert routh_b == 1440 and routh_c == sp.Rational(64000, 9)
report = {
    'direct_characteristic_exact': str(sp.factor(p)),
    'filtered_characteristic_exact': str(q),
    'filtered_roots_per_s': [{'real': z.real, 'imag': z.imag} for z in roots],
    'dominant_oscillation_hz': pair.imag/(2*math.pi),
    'dominant_envelope_decay_time_s': -1/pair.real,
    'dominant_damping_ratio': -pair.real/abs(pair),
    'filter_time_constant_s': .05,
    'actuator_time_constant_s': .0125,
    'same_homogeneous_matrix_for_both_filtered_laws': True,
    'routh_first_column_exact': ['1', '100', str(routh_b), str(routh_c), '1280000'],
    'scope': 'Exact symbolic characteristic polynomials plus numerical roots for the fixed r=80,lambda=20 model. No stale timestamp, sensor delay, saturation, integral action, or different controller tuning is introduced. Not a Lean theorem or general instability claim.'}
Path(__file__).with_name('result.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report, indent=2))
