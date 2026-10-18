#!/usr/bin/env python3
"""Exact arithmetic diagnostic; not a formal proof of the coarse norm bound."""
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
P = [[F(x) for x in row] for row in [
    ['38/5', '257/25', '5'], ['257/25', '1319/50', '769/50'],
    ['5', '769/50', '278/25']]]
rates = [F(9, 10), F(1), F(11, 10)]
squares = [F(81, 100), F(99, 100), F(121, 100)]
rows = []
for i in range(3):
    for h in [F(0), F(1, 5)]:
        for theta in [F(0), F(1)]:
            v = [(F(1, 2)-theta)*h, theta*rates[i]*h,
                 rates[i]-theta*squares[i]*h]
            norm = sum(x*x for x in v)
            energy = sum(v[j]*P[j][k]*v[k] for j in range(3) for k in range(3))
            rows.append({'rate_coefficient': i, 'elapsed': str(h),
                         'remainder': str(theta), 'vector': list(map(str, v)),
                         'squared_norm': str(norm), 'energy': str(energy)})
M = sum(P[i][i] for i in range(3))
maxnorm = max(F(x['squared_norm']) for x in rows)
eta = F(15, 902)
assert maxnorm == F(61, 50) and M*maxnorm == F(27511, 500)
budgets = []
for name, C, W in [('coarse', M*maxnorm, F(1, 100)),
                   ('direct', F(16), F(1, 100)),
                   ('direct-larger', F(16), F(1, 90))]:
    D = C*(F(1, 5)+1/eta)*W*W
    budgets.append({'method': name, 'C': str(C), 'W': str(W),
                    'D': str(D), 'threshold': str(12*eta), 'passes': D <= 12*eta})
source = ROOT/'lean-controls/LeanControls/UncertainResponse.lean'
data = {'scope': 'Exact Fraction arithmetic diagnostic. Direct response-energy and final budget comparisons have separate Lean proofs. This file is not a formal proof of the coarse norm bound.',
        'response_source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
        'vertices': rows, 'maximum_squared_norm': str(maxnorm),
        'maximum_vertex_energy': str(max(F(x['energy']) for x in rows)),
        'trace_bound': str(M), 'budgets': budgets}
Path(__file__).with_name('response-ablation.json').write_text(json.dumps(data, indent=2)+'\n')
print('Exact response ablation: coarse budget fails; direct budgets pass.')
