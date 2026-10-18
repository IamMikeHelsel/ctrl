#!/usr/bin/env python3
"""Illustrative SI-unit comparison. Floating-point results are not Lean proofs.

Assumptions/cases were recorded in research-target.txt before this script.
Only the separate Lean files certify the displayed 0.40 m/s case.
"""
import hashlib
import json
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent
POSITION_ERROR = 0.001
VELOCITY_ERROR = 0.01
DELAY = 0.05
PENDING_ACCEL = 0.1
CLEARANCE = 0.15
RLO, RHI = 8.0, 12.0
BLO, BHI = -2.0, -1.2


def engagement(vhat):
    v = vhat + VELOCITY_ERROR
    return (POSITION_ERROR + v * DELAY + PENDING_ACCEL * DELAY**2 / 2,
            v + PENDING_ACCEL * DELAY, PENDING_ACCEL)


def held(t, z, rate, target):
    x, v, a = z
    one_minus_exp = -math.expm1(-rate * t)
    return (x + v*t + target*t*t/2 + (a-target)*(t/rate-one_minus_exp/rate**2),
            v + target*t + (a-target)*one_minus_exp/rate,
            target + (a-target)*math.exp(-rate*t))


def flow_stop(z, rate, target):
    assert z[1] >= 0 and target < 0
    lo, hi = 0.0, 1.0
    while held(hi, z, rate, target)[1] > 0:
        hi *= 2
    for _ in range(70):
        mid = (lo+hi)/2
        if held(mid,z,rate,target)[1] > 0:
            lo = mid
        else:
            hi = mid
    t = (lo+hi)/2
    return {'time_from_request_s': DELAY+t, 'peak_position_m': held(t,z,rate,target)[0]}


def comparison(vhat):
    z = engagement(vhat)
    w = z[1] + (z[2]-BHI)/RLO
    entries = {
        'instantaneous_nominal_approximation': {
            'peak_position_m': z[0]+z[1]**2/(-2*BLO),
            'time_from_request_s': DELAY+z[1]/(-BLO)},
        'fixed_nominal_model': flow_stop(z,10.0,BLO),
        'lag_only_uncertainty': flow_stop(z,RLO,BLO),
        'varying_rate_and_strength_envelope': flow_stop(z,RLO,BHI),
        'simple_conservative_same_assumptions': {
            'peak_position_m': z[0]+w*w/(-2*BHI),
            'time_from_request_s': DELAY+w/(-BHI)}}
    for item in entries.values():
        item['passes_clearance_numerically'] = item['peak_position_m'] <= CLEARANCE
    return {'estimated_velocity_m_s':vhat,'engagement_upper':z,'methods':entries}


def threshold(method):
    lo, hi = 0.0, 1.0
    for _ in range(60):
        mid = (lo+hi)/2
        if comparison(mid)['methods'][method]['peak_position_m'] <= CLEARANCE:
            lo = mid
        else:
            hi = mid
    return lo


TRACES = [
    ('slow_weak_endpoint', lambda t:8., lambda t:-1.2, True),
    ('fast_strong_endpoint',lambda t:12.,lambda t:-2.,True),
    ('smooth_rate_and_target',lambda t:10.+2.*math.sin(11.*t),
     lambda t:-1.6+0.4*math.sin(7.*t),True),
    ('progressive_strength_loss',lambda t:10.+2.*math.cos(9.*t),
     lambda t:-1.2-0.8*math.exp(-6.*t),True),
    ('out_of_contract_strength',lambda t:8.,lambda t:-0.9,False)]


def rk4(t,z,dt,rate,target):
    def rhs(s,q): return (q[1],q[2],rate(s)*(target(s)-q[2]))
    def add(q,k,h): return tuple(a+h*b for a,b in zip(q,k))
    k1=rhs(t,z);k2=rhs(t+dt/2,add(z,k1,dt/2))
    k3=rhs(t+dt/2,add(z,k2,dt/2));k4=rhs(t+dt,add(z,k3,dt))
    return tuple(a+dt*(b+2*c+2*d+e)/6 for a,b,c,d,e in zip(z,k1,k2,k3,k4))


def trace(rate,target,n):
    horizon=0.8;dt=horizon/n;z=engagement(0.4);samples=[(0.,*z)];stop=None
    max_excess=-math.inf
    for k in range(n):
        t=k*dt;next_z=rk4(t,z,dt,rate,target)
        if stop is None and z[1]>0>=next_z[1]:
            lo,hi=0.,dt
            for _ in range(45):
                mid=(lo+hi)/2
                if rk4(t,z,mid,rate,target)[1]>0:lo=mid
                else:hi=mid
            ts=(lo+hi)/2;zs=rk4(t,z,ts,rate,target)
            stop={'time_from_request_s':DELAY+t+ts,'peak_position_m':zs[0]}
        z=next_z
        up=held(t+dt,engagement(.4),RLO,BHI)
        max_excess=max(max_excess,max(z[i]-up[i] for i in range(3)))
        if (k+1)%max(1,n//400)==0:samples.append((t+dt,*z))
    return {'stop':stop,'maximum_grid_coordinate_excess_over_upper':max_excess,'samples':samples}


def svg(traces):
    W,H=1020,590;left,right,top,bottom=82,980,90,468
    def pt(t,x):return (left+(right-left)*t/.85,bottom-(bottom-top)*x/.22)
    parts=[f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}">',
      '<rect width="100%" height="100%" fill="#fffef9"/>',
      '<g font-family="Arial,sans-serif" fill="#20372f">',
      '<text x="40" y="35" font-size="25">How much room does changing response need?</text>',
      '<text x="40" y="61" font-size="15">Illustration: 0.40 m/s estimate · ±0.01 m/s error · 50 ms delay · synthetic powered axis</text>']
    for cm in range(0,23,5):
        y=pt(0,cm/100)[1]
        parts += [f'<path d="M {left} {y} H {right}" stroke="#dce3dc"/>',f'<text x="35" y="{y+5}" font-size="13">{cm} cm</text>']
    for i in range(9):
        x=pt(i/10,0)[0];parts.append(f'<text x="{x-10}" y="{bottom+23}" font-size="13">{i/10:.1f}</text>')
    wall=pt(0,CLEARANCE)[1]
    parts += [f'<path d="M {left} {wall} H {right}" stroke="#ad5439" stroke-width="2" stroke-dasharray="6 5"/>',
      f'<text x="{left+8}" y="{wall-9}" font-size="14" fill="#963f2c">15 cm travel limit</text>']
    colors=['#245d40','#4c8f96','#9b8f45','#7764a7','#bd6840']
    for record,color in zip(traces,colors):
        samples=record['samples'];stop=record['stop'];tstop=stop['time_from_request_s']-DELAY
        prefix=[(0,POSITION_ERROR),(DELAY,engagement(.4)[0])]
        points=prefix+[(t+DELAY,x)for t,x,v,a in samples if t<=tstop]+[(stop['time_from_request_s'],stop['peak_position_m'])]
        coords=' '.join(f'{pt(t,x)[0]:.2f},{pt(t,x)[1]:.2f}' for t,x in points)
        parts.append(f'<polyline points="{coords}" fill="none" stroke="{color}" stroke-width="3"/>')
        x,y=pt(stop['time_from_request_s'],stop['peak_position_m'])
        parts.append(f'<circle cx="{x}" cy="{y}" r="4" fill="{color}"/>')
    labels=['Weak/slow upper response','Strong/fast response','Changing rate and strength','Progressive strength loss','Outside assumed strength bound']
    for i,(label,color) in enumerate(zip(labels,colors)):
        x=45+(i%3)*325;y=530+(i//3)*26
        parts.extend([f'<path d="M {x} {y-5} h 24" stroke="{color}" stroke-width="3"/>',f'<text x="{x+31}" y="{y}" font-size="13">{label}</text>'])
    parts += ['<text x="700" y="505" font-size="13">Seconds from stop request</text>',
      '</g></svg>']
    (HERE/'response-comparison.svg').write_text('\n'.join(parts))


def main():
    cases=[comparison(v)for v in [.3,.4,.5]]
    trace_records=[]
    for name,r,b,admitted in TRACES:
        coarse=trace(r,b,2000);fine=trace(r,b,4000)
        item={'name':name,'inside_stated_contract':admitted,**fine,
              'refinement_peak_change_m':abs(fine['stop']['peak_position_m']-coarse['stop']['peak_position_m'])}
        if admitted:assert fine['maximum_grid_coordinate_excess_over_upper']<1e-8
        assert item['refinement_peak_change_m']<1e-7
        trace_records.append(item)
    # Constant endpoint checks expose numerical integration errors.
    endpoint=flow_stop(engagement(.4),RLO,BHI)
    assert abs(trace_records[0]['stop']['peak_position_m']-endpoint['peak_position_m'])<1e-8
    data={'scope':'Synthetic, floating-point comparison; numerical thresholds and traces are not formal certificates.',
          'target_sha256':hashlib.sha256((HERE/'research-target.txt').read_bytes()).hexdigest(),
          'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'parameters':{'position_error_m':POSITION_ERROR,'velocity_error_m_s':VELOCITY_ERROR,
          'maximum_delay_s':DELAY,'pending_acceleration_upper_m_s2':PENDING_ACCEL,
          'rate_range_per_s':[RLO,RHI],'target_range_m_s2':[BLO,BHI],'clearance_m':CLEARANCE},
          'cases':cases,'numerical_velocity_estimate_thresholds':{k:threshold(k)for k in cases[0]['methods']},
          'traces':trace_records}
    (HERE/'results.json').write_text(json.dumps(data,indent=2)+'\n');svg(trace_records)
    print(json.dumps({'cases':cases,'thresholds':data['numerical_velocity_estimate_thresholds'],
      'traces':[{k:v for k,v in t.items()if k!='samples'}for t in trace_records]},indent=2))


if __name__=='__main__':main()
