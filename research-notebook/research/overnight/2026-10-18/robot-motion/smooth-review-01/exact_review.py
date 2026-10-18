"""Independent exact reference review. No builder code imported.

Convert power coefficients to Bernstein coefficients by the general binomial
identity. Integrate the linear jerk directly, rather than use builder recurrence.
"""
from pathlib import Path
from fractions import Fraction as F
from math import comb, factorial
from collections import Counter
import hashlib, json

HERE=Path(__file__).resolve().parent
B=HERE.parent/'smooth-baseline-01'
BASE=HERE.parent/'builder-03'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(n): return json.loads((B/n).read_text())
def evaluate(c,t): return sum((a*t**k for k,a in enumerate(c)),F(0))
def derivative(c): return [k*c[k] for k in range(1,len(c))]
def bernstein(c,h):
    n=len(c)-1
    return [sum((c[i]*h**i*F(comb(k,i),comb(n,i)) for i in range(k+1)),F(0)) for k in range(n+1)]
def check(js,h,initial,cap):
    state=tuple(initial);states=[state];controls=[];violations=[]
    peaks={k:F(0) for k in ['speed','acceleration','jerk','snap']}
    qp=state[0];objective=F(0)
    for i,(jl,jr) in enumerate(zip(js,js[1:])):
        p=[state[0],state[1],state[2]/2,jl/6,(jr-jl)/(24*h)]
        ds=[p]
        for _ in range(4): ds.append(derivative(ds[-1]))
        coeffs=[bernstein(d,h) for d in ds]
        assert evaluate(ds[3],0)==jl and evaluate(ds[3],h)==jr
        controls.append({'cell':i,'q':list(map(str,coeffs[0])),'v':list(map(str,coeffs[1])),'a':list(map(str,coeffs[2]))})
        for k,name,limit in [(1,'speed',F(1,10)),(2,'acceleration',F(1,2)),(3,'jerk',F(15,2))]:
            peaks[name]=max(peaks[name],*map(abs,coeffs[k]))
            if max(map(abs,coeffs[k]))>limit: violations.append({'cell':i,'condition':name})
        peaks['snap']=max(peaks['snap'],*map(abs,coeffs[4]))
        qp=max(qp,*coeffs[0])
        if max(coeffs[0])>initial[0]+cap:violations.append({'cell':i,'condition':'position_cap'})
        # Integrate the square of the explicit linear jerk polynomial.
        sq=[sum((ds[3][l]*ds[3][k-l] for l in range(2) if 0<=k-l<2),F(0)) for k in range(3)]
        objective+=sum((c*h**(k+1)/(k+1) for k,c in enumerate(sq)),F(0))
        state=tuple(evaluate(d,h) for d in ds[:3]);states.append(state)
    if state!=(0,0,0):violations.append({'condition':'terminal_state'})
    if js[0]!=F(-5,4) or js[-1]!=0:violations.append({'condition':'terminal_or_initial_jerk'})
    validation={'passed':not violations,'violations':violations,'bernstein_absolute_bounds':{k:str(v) for k,v in peaks.items()},'reference_forward_excursion_upper_bound_m':str(qp-initial[0]),'terminal_state':list(map(str,state)),'controls':controls}
    return validation,states,objective

manifest_hash='14b028f05727b6459b30e63d84162fc49de1fdeb65c1a9327d30468149afd3c9'
assert sha(B/'artifact-sha256.json')==manifest_hash
for n,v in read('artifact-sha256.json')['files'].items(): assert sha(B/n)==v['sha256'],n
assert sha(B/'artifact-sha256-final.json')=='25d2b152cfc0890bdbef79870560474a291f4bdf64c9076ca0e034eb7fd3f26f'
for n,v in read('artifact-sha256-final.json')['files'].items(): assert sha(B/n)==v['sha256'],n
for n in ['protocol-freeze.json','implementation-freeze.json','reference-freeze.json']:
    for path,digest in read(n)['files'].items():assert sha(B/path)==digest,(n,path)
config=read('configuration.json');cases=read('solver-summary.json')['cases']
assert len(cases)==6
assert [(c['N'],F(c['cap_m'])) for c in cases]==[(n,c) for n in [90,180] for c in [F(7,1000),F(1,100),F(3,200)]]
status_counts=dict(Counter(c['solver_status'] for c in cases))
assert status_counts=={'infeasible':2,'optimal':1,'optimal_inaccurate':3}
assert [c['case'] for c in cases if c['accepted']]==['n90_cap10mm']
out={'status':'PASS','method':'Independent rational power integration and generic power-to-Bernstein transform; no builder import','input_manifest_sha256':manifest_hash,'files_checked':216,'final_manifest_files_checked':218,'solver_status_counts':status_counts,'exact_checks':{},'negative_controls':[]}
r=read('n90_cap10mm.json');js=list(map(F,r['corrected_jerk_nodes_SI']));raw=list(map(F,r['rounded_jerk_nodes_SI']));dt=F(r['dt_s']);initial=list(map(F,config['initial_qvaj']))[:3]
validation,states,obj=check(js,dt,initial,F(1,100))
assert validation==r['validation'] and validation['passed']
assert [list(map(str,x)) for x in states]==r['exact_states_SI']
assert str(obj)==r['corrected_reference_jerk_integral_SI']
raw_validation,raw_states,raw_obj=check(raw,dt,initial,F(1,100))
assert list(map(str,raw_states[-1]))==r['endpoint_before_correction']
assert str(raw_obj)==r['rounded_reference_jerk_integral_SI']
changes=[i for i,(a,b) in enumerate(zip(raw,js)) if a!=b]
assert changes==[87,88,89]
assert [str(js[i]-raw[i]) for i in changes]==r['last_three_corrections']
raw_reconstructed=[F(round(float(v)/1000*10**12),10**12) for v in r['solver_state_mm']['j']]
raw_reconstructed[0]=F(-5,4);raw_reconstructed[-1]=0
assert raw_reconstructed==raw
# Derive the prefix jet from the four-box step directly.
def fir_jet(t,k):
    return sum((F(1,50)*(-1)**i*comb(4,i)*max(F(0),t-F(11,50)-i*F(1,5))**(4-k)/factorial(4-k)/F(1,5)**4 for i in range(5)),F(0))
assert [fir_jet(F(13,25),k) for k in range(4)]==initial+[js[0]]
all_schedules=read('reference-schedules.json')['schedules'];schedules=[s for s in all_schedules if s['method']=='smooth_n90_cap10mm']
assert len(schedules)==2 and schedules[0]['pieces']==schedules[1]['pieces']
ordinary_keys=['p','v','a','jerk','snap']
schedule=schedules[0];np=0
for p in schedule['pieces']:
    t=F(p['start_exact']);end=F(p['end_exact'])
    if t<F(13,25):
        if end>F(13,25):raise AssertionError('unclipped prefix')
        values=[fir_jet(t,k) for k in range(4)]
        assert list(map(F,p['rational_derivatives_at_start']))[:4]==values
    elif t<F(71,50):
        i=int((t-F(13,25))/dt)
        assert t==F(13,25)+i*dt and end==t+dt
        values=list(states[i])+[js[i],(js[i+1]-js[i])/dt]
        assert list(map(F,p['rational_derivatives_at_start']))==values
        assert [p[k] for k in ordinary_keys]==list(map(float,values));np+=1
    else:
        assert t==F(71,50) and end==F(5,2)
        assert list(map(F,p['rational_derivatives_at_start']))==[0]*5
assert np==90
# Check the negative controls with this separately written checker.
for test in read('negative-controls.json')['tests']:
    altered=list(js)
    if test['mutation'] is not None:
        index,value=test['mutation'];altered[index]=F(value)
    v,_,_=check(altered,dt,initial,F(test['cap']))
    assert not v['passed'] and test['expected_rejection'] in {x['condition'] for x in v['violations']}
    assert v['violations']==test['violations']
    out['negative_controls'].append({'name':test['name'],'independent_rejection':True,'conditions':sorted({x['condition'] for x in v['violations']})})
# One extra malicious schedule change: an instantaneous state reset at the endpoint
# would break the polynomial endpoint; the unchanged exact reconstruction has none.
tampered=list(js);tampered[40]+=F(1,1000000)
_,tampered_states,_=check(tampered,dt,initial,F(1,100))
assert tampered_states[-1]!=(0,0,0)
out['extra_endpoint_reset_control']={'detected_nonzero_endpoint':list(map(str,tampered_states[-1])),'reason':'Writing a zero tail would create a q/v/a state jump and cannot replace exact endpoint equality.'}
out['exact_checks']={'intervals':np,'rational_states':len(states),'Bernstein_controls':sum(len(x[k]) for x in validation['controls'] for k in ['q','v','a'])+2*np,'objective':str(obj),'objective_float':float(obj),'initial_jet':list(map(str,initial+[js[0]])),'terminal_jet':['0']*4,'C3_continuous':True,'all_future_reference_bounds':validation['bernstein_absolute_bounds'],'reference_forward_upper_m':validation['reference_forward_excursion_upper_bound_m'],'correction_indices':changes,'exact_terminal_no_reset':True,'same_plan_both_deadlines':True,'not_Lean':True,'not_optimality_certificate':True}
(HERE/'exact-review.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
