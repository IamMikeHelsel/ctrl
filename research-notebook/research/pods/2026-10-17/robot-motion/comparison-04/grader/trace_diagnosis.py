#!/usr/bin/env python3
"""Exact checks of two features of the existing hold fixture; no new cases."""
from pathlib import Path
from fractions import Fraction as Q
import json
H=Path(__file__).resolve().parent;B=H.parent/'builder'
spec=json.loads((B/'frozen-fixed-streams.json').read_text())
checks=json.loads((B/'frozen-reference-checks.json').read_text())
events=[(Q(e['time_s']),Q(e['delta_m'])) for e in next(c for c in checks['cases'] if c['case']=='hold_jitter')['accepted_events']]
h=Q(spec['h_s']);tick=Q(spec['commit_tick_s']);assert h/(2*tick)==5
# One box average of the existing piecewise-constant target, computed by exact integration.
def box(t):return sum((d*(max(Q(0),t-tau)-max(Q(0),t-tau-h))/h for tau,d in events),Q(0))
lo=events[0][0]+h;hi=events[-1][0]
knots=sorted({lo,hi}|{x for tau,d in events for x in [tau,tau+h] if lo<=x<=hi})
assert all(box(t)==0 for t in knots)
# On each interval between those breakpoints the one-box average is affine,
# so zero at both endpoints gives exact zero throughout that interval.
native=json.loads((H/'native-hold_jitter-output.json').read_text())['commits']
exports=json.loads((B/'ruckig-primary-exports.json').read_text())['hold_jitter']
p=v=a=Q(0);prefix=[]
for k in range(6):
    assert exports[k]['plan']['phases'][1]['jerk']==float(((-1)**k)*Q(15,2))
    # The executed first six intervals each retain their first constant jerk.
    positive=[q for q in exports[k]['plan']['phases'] if q['duration']>0]
    assert Q(positive[0]['end'])>=tick
    j=Q(15,2)*(-1)**k
    p,v,a=p+v*tick+a*tick**2/2+j*tick**3/6,v+a*tick+j*tick**2/2,a+j*tick
    observed=native[k+1]
    residual=[abs(float(z)-observed[key]) for z,key in zip([p,v,a],['current_p','current_v','current_a'])]
    assert all(x<1e-14 for x in residual)
    prefix.append({'commit':str(events[k+1][0]),'previous_jerk':str(j),'expected_q_v_a':list(map(str,[p,v,a])),'native_residual_q_v_a':residual})
out={'scope':'Existing fixed hold-jitter fixture only; exact rational checks plus native floating-state comparisons. Not a Lean theorem and not a new experiment.',
 'period_s':str(2*tick),'box_width_s':str(h),'full_periods_in_box':str(h/(2*tick)),
 'single_box_exact_zero_interval_s':[str(lo),str(hi)],'single_box_checked_breakpoints':list(map(str,knots)),
 'first_six_native_intervals':prefix,
 'interpretation':'Alternating first-segment jerk returns acceleration to zero every second replan while velocity accumulates during this prefix. The later native trajectory changes this pattern. No universal Ruckig mechanism is claimed.',
 'required_qualification':'The fixed FIR width contains exactly five noise periods. This special cancellation and the 800 ms tail prevent a general superiority claim.'}
(H/'trace-diagnosis.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'passed':True,'exact_prefix_end_q_v_a':list(map(str,[p,v,a])),'single_box_zero_interval':out['single_box_exact_zero_interval_s']}))
