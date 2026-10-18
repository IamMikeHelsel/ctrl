#!/usr/bin/env python3
"""Exact rational binding of frozen native06 cubics; no physical simulation."""
from pathlib import Path
from fractions import Fraction as Q
from datetime import datetime, timezone
import json, hashlib

HERE = Path(__file__).resolve().parent
BASE = HERE.parent.parent / 'native-execution-06' / 'builder'
FROZEN = 'aaae586029babf2e9381d09ff34fb7b488495630c48abde27ab9b4d8ece1a803'
SIGMA, J, W, R0, B = Q(10), Q(15,2), Q(1,100), Q(41,320000), Q(1,10**15)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def at(c,t):
    p,v,a,j = c
    return (p+v*t+a*t*t/2+j*t*t*t/6, v+a*t+j*t*t/2, a+j*t)
def coords(d):
    p,v,a=d
    return (p,p+v/(4*SIGMA),p+v/(2*SIGMA)+a/(16*SIGMA**2))
def main():
    manifest = BASE/'artifact-sha256.json'; source=BASE/'reference-schedules.json'
    assert sha(manifest)==FROZEN
    m=json.loads(manifest.read_text()); assert sha(source)==m['files']['reference-schedules.json']
    before=sha(source); data=json.loads(source.read_text())['schedules']; outputs=[]
    assert W+J/(48*SIGMA)==2*SIGMA**2*R0
    for s in data:
        if s['method'] not in ['ruckig','ruckig_min_08']: continue
        pieces=[]; jumps=[]; previous=None; total=Q(0)
        for k,p in enumerate(s['pieces']):
            start,end=Q(p['start_exact']),Q(p['end_exact']); dt=end-start
            # Q(float) retains the exact binary coefficient, not decimal rounding.
            coeff=tuple(Q(p[n]) for n in ['p','v','a','jerk'])
            assert dt>0 and Q(p['snap'])==0 and abs(coeff[3])<=J
            if previous is None:
                assert start==0 and coeff[:3]==(Q(0),Q(0),Q(0))
            else:
                assert previous['end']==start
                left=at(previous['coeff'],previous['duration'])
                delta=tuple(b-a for a,b in zip(left,coeff[:3]))
                z=coords(delta); reserve=max(map(abs,z)); assert reserve<=B
                total+=reserve
                jumps.append({'left_piece':k-1,'right_piece':k,'time':str(start),
                    'left_endpoint':[str(x) for x in left], 'right_endpoint':[str(x) for x in coeff[:3]],
                    'delta_q_v_a':[str(x) for x in delta], 'transformed_delta':[str(x) for x in z],
                    'exact_radius':str(reserve), 'uniform_radius_check':reserve<=B})
            pieces.append({'index':k,'start':str(start),'end':str(end),'duration':str(dt),
                'coefficients_p_v_a_j':[str(x) for x in coeff], 'origin':p['origin']})
            previous={'end':end,'duration':dt,'coeff':coeff}
        assert previous['end']==Q(s['horizon_exact'])
        uniform=len(jumps)*B
        assert total<=uniform and R0+uniform<Q(1,5000)
        outputs.append({'case':s['case'],'method':s['method'],'piece_count':len(pieces),
            'join_count':len(jumps),'horizon':s['horizon_exact'],'pieces':pieces,'joins':jumps,
            'exact_sum_jump_radius':str(total),'exact_sum_jump_radius_m':float(total),
            'uniform_sum_jump_radius':str(uniform),'uniform_sum_jump_radius_m':float(uniform),
            'conditional_position_radius':str(R0+uniform),'conditional_position_radius_mm':float((R0+uniform)*1000),
            'target_tracking_band':str(Q(1,5000))})
    assert len(outputs)==12 and sum(s['piece_count'] for s in outputs)==886
    assert sha(source)==before and sha(manifest)==FROZEN
    result={'status':'exact rational data checks passed; no Lean/native/physical execution theorem inferred',
        'checked_utc':datetime.now(timezone.utc).isoformat(), 'source_manifest_sha256':FROZEN,
        'source_schedule_sha256':before,'script_sha256':sha(Path(__file__)),
        'constants':{k:str(v) for k,v in {'sigma':SIGMA,'J':J,'W':W,'R0':R0,'per_join_allowance':B}.items()},
        'bound_choice':'Conservative 1e-15 m transformed allowance chosen from previously frozen06 join audit, before this exact binding computation. It is not a new empirical-performance hypothesis.',
        'cases':outputs,'total_pieces':sum(x['piece_count'] for x in outputs),
        'total_joins':sum(x['join_count'] for x in outputs),
        'scope':'Polynomial interpretation of frozen exported binary coefficients and clocks. Actual physical state must match at joins; all trajectory and plant assumptions remain. Not exact native at_time arithmetic at all real times, firmware behavior, task-goal bound, or acceleration-limit certificate.'}
    (HERE/'exact-reserve.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'cases':len(outputs),'pieces':result['total_pieces'],'joins':result['total_joins'],
        'max_exact_sum_m':max(x['exact_sum_jump_radius_m'] for x in outputs),
        'max_uniform_sum_m':max(x['uniform_sum_jump_radius_m'] for x in outputs),
        'max_conditional_radius_mm':max(x['conditional_position_radius_mm'] for x in outputs)},indent=2))
if __name__=='__main__':main()
