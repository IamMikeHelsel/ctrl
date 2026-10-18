"""Exact candidate arithmetic; not a Lean theorem or independent review."""
from pathlib import Path
from fractions import Fraction as Q
from math import comb
import hashlib
import json

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent/'lead-01/reference-checks.json'
case = json.loads(SOURCE.read_text())['cases'][0]
assert case['case'] == 'hold_jitter'
events = [(Q(a['commit_s']), Q(a['delta_m'])) for a in case['outcomes']
          if a['outcome'] == 'accepted' and Q(a['delta_m'])]
assert all(t >= 0 for t,d in events) and sum(d for t,d in events) == 0
h = Q(1,5)
knots = sorted({Q(0)} | {t+m*h for t,d in events for m in range(5)})
lo, hi = Q(0), Q(0)
for left, right in zip(knots, knots[1:]):
    poly = [Q(0)]*5
    for tau, delta in events:
        for m in range(5):
            root = tau+m*h
            if root <= left:
                weight = delta*(-1)**m*comb(4,m)/(24*h**4)
                for k in range(5):
                    poly[k] += weight*comb(4,k)*(left-root)**(4-k)*(right-left)**k
    bernstein = [sum(poly[k]*Q(comb(i,k),comb(4,k)) for k in range(i+1))
                 for i in range(5)]
    lo, hi = min(lo,min(bernstein)), max(hi,max(bernstein))
qbound = max(-lo, hi)
assert qbound == Q(401,12000000)
budgets = []
for name, J in [('unchanged_gate_limit',Q(15,2)),
                ('maximum_prefix_admission_bound',max(Q(a['future_reference_jerk_peak_m_s3'])
                  for a in case['outcomes'] if a['outcome']=='accepted'))]:
    radius = (Q(1,100)+J/480)/200
    total = qbound+radius
    assert total <= Q(1,5000)
    budgets.append({'choice':name, 'reference_jerk_limit':str(J),
                    'tracking_radius_min_m':str(radius),
                    'combined_absolute_hold_bound_m':str(total)})
result = {'status':'candidate exact arithmetic; q-bound-to-reference and physical composition still need Lean checking',
          'reference_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
          'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'reference_position_lower_m':str(lo), 'reference_position_upper_m':str(hi),
          'budget_choices':budgets, 'physical_hold_target_m':'1/5000',
          'event_count':len(events), 'closed_cells':len(knots)-1,
          'tail_start_s':str(knots[-1]), 'tail_position_m':'0',
          'scope':'Same fixed hold-jitter input and controller. These are derived certificate radii, not retuned controller gains. The general gate does not establish this true-goal bound for arbitrary target histories.'}
(HERE/'hold-bound-candidate.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
