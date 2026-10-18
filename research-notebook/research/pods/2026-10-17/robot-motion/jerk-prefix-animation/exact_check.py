"""Check the ideal six-interval reference prefix against the frozen review."""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
REVIEW = HERE.parent / 'comparison-04/grader'
diagnosis = json.loads((REVIEW/'trace-diagnosis.json').read_text())
q = v = a = F(0)
h = F(1, 50)
start = F(11, 50)
segments = []
for k in range(6):
    j = F(15, 2) * (-1 if k % 2 else 1)
    segments.append({'start_elapsed_s': str(k*h), 'duration_s': str(h),
                     'q0_m': str(q), 'v0_m_s': str(v), 'a0_m_s2': str(a),
                     'jerk_m_s3': str(j)})
    q, v, a = q+v*h+a*h*h/2+j*h**3/6, v+a*h+j*h*h/2, a+j*h
    recorded = diagnosis['first_six_native_intervals'][k]
    assert [q, v, a] == list(map(F, recorded['expected_q_v_a']))
    assert start+(k+1)*h == F(recorded['commit'])
    assert j == F(recorded['previous_jerk'])
    assert a in (F(0), F(3, 20))
assert (q, v, a) == (F(27, 50000), F(9, 1000), F(0))
result = {
    'scope': 'Exact ideal polynomial reference prefix only; no physical-axis simulation.',
    'absolute_start_s': str(start), 'duration_s': str(6*h),
    'segments': segments,
    'end_q_m': str(q), 'end_v_m_s': str(v), 'end_a_m_s2': str(a),
    'all_six_review_endpoints_match_exactly': True,
    'acceleration_range_m_s2': ['0', '3/20'],
    'reason_acceleration_range_holds': 'Each interval has constant signed jerk, so acceleration is affine and lies between its two checked endpoint values.',
    'input_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in
                     [REVIEW/'review-report.txt', REVIEW/'trace-diagnosis.json']},
    'not_a_lean_proof': True,
}
(HERE/'exact-check.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k != 'segments'}, indent=2))
