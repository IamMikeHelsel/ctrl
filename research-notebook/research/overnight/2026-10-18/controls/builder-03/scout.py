"""Bounded adversarial search. No search output is a mathematical certificate."""
from pathlib import Path
import ctypes as ct, datetime as dt, hashlib, itertools, json, platform, sys, time
from fractions import Fraction
import numpy as np
import scipy
from scipy.optimize import minimize, minimize_scalar

BASE=Path(__file__).resolve().parent
K=ct.CDLL(str(BASE/'.cache/scout_kernel.dylib'))
P=np.ctypeslib.ndpointer(dtype=np.float64,ndim=1,flags='C_CONTIGUOUS')
K.adverse.argtypes=[ct.c_int,P,P,ct.c_double,ct.c_int,ct.c_double,P,P]
K.adverse.restype=ct.c_double
K.forward.argtypes=[ct.c_int,P,P,P,ct.c_int,P,P,ct.c_double,P]
K.forward.restype=None
TIMES=np.arange(4001,dtype=float)/1000
GRID=np.arange(401,dtype=float)/100
VERTICES=[np.array(v,dtype=float)*.0002 for v in itertools.product([-1,1],repeat=3)]
VERTICES.append(np.zeros(3))

def utc():return dt.datetime.now(dt.timezone.utc).isoformat()
def arr(v):return np.ascontiguousarray(v,dtype=float)
def adverse(knots,rate,target,component,step=.001):
    weights=np.zeros(len(knots));coefs=np.zeros(3)
    value=K.adverse(len(knots),arr(knots),arr(rate),target,component,step,weights,coefs)
    return value,weights,coefs
def initial(z):return arr([z[0],z[1]-z[0],z[2]-2*z[1]+z[0]])
def forward(knots,rate,w,z,times=TIMES,step=.001):
    states=np.empty(len(times)*3)
    K.forward(len(knots),arr(knots),arr(rate),arr(w),len(times),arr(times),initial(z),step,states)
    return states.reshape((-1,3))
def rational(v):return str(Fraction(str(float(v))).limit_denominator(10**9))
def evaluate(knots,rate,target,component,label):
    rate=np.clip(np.round(rate,6),80,120)
    value,weights,coefs=adverse(knots,rate,target,component)
    w=.01*np.sign(weights)
    # Preserve the target endpoint value for the unsearched suffix.
    ix=np.searchsorted(knots,target,side='right')-1
    w[ix+1:]=w[ix]
    summaries=[];winner=None
    for z in VERTICES:
        states=forward(knots,rate,w,z)
        values=np.abs(states[2000:,1:])*np.array([40000,80000])
        ti,ci=np.unravel_index(np.argmax(values),values.shape)
        s={'z':z.tolist(),'probe_ratio':float(values[ti,ci]),'probe_time':float(TIMES[2000+ti]),
           'component':int(ci+1),'max_v_mps':float(np.max(np.abs(states[2000:,1]))*40),
           'max_a_mps2':float(np.max(np.abs(states[2000:,2]))*1600)}
        summaries.append(s)
        if winner is None or s['probe_ratio']>winner['probe_ratio']:winner=s
    result={'label':label,'created_utc':utc(),'target_time':target,'target_component':component,
            'adjoint_ratio':value,'adjoint_z':(.0002*np.sign(coefs)).tolist(),
            'vertices':summaries,'winner':winner,'knots':knots.tolist(),
            'rate':rate.tolist(),'disturbance':w.tolist()}
    (BASE/'candidates'/f'{label}.json').write_text(json.dumps(result,indent=2)+'\n')
    return result

def local_peak(candidate):
    win=candidate['winner'];t=win['probe_time'];ci=win['component'];z=arr(win['z'])
    knots=arr(candidate['knots']);rate=arr(candidate['rate']);w=arr(candidate['disturbance'])
    def val(t):return abs(forward(knots,rate,w,z,arr([t]))[0,ci])*(40000 if ci==1 else 80000)
    opt=minimize_scalar(lambda s:-val(s),bounds=(max(2,t-.002),min(4,t+.002)),method='bounded',
                        options={'xatol':1e-11,'maxiter':80})
    choices=[max(2,t-.002),min(4,t+.002),float(opt.x),t]
    best=max(choices,key=val);fixed=round(best,6)
    return {'target_time':fixed,'component':ci,'ratio':val(fixed),
            'unrounded_peak_time':best,'z':win['z']}

class Budget(Exception):pass
def optimize_rates(knots,decode,x0,target,component,budget,label):
    best=[-float('inf'),None];calls=0;history=[];started=time.monotonic()
    def objective(p):
        nonlocal calls
        if calls>=budget or dt.datetime.now(dt.timezone.utc)>=dt.datetime(2026,10,18,8,30,tzinfo=dt.timezone.utc):
            raise Budget()
        calls+=1;v=adverse(knots,decode(p),target,component)[0]
        if v>best[0]:best[:]=[v,p.copy()]
        history.append({'call':calls,'ratio':v})
        return -v
    try:
        res=minimize(objective,x0,method='L-BFGS-B',bounds=[(80,120)]*len(x0),
                     options={'maxfun':budget,'maxiter':100,'ftol':1e-12,'gtol':1e-8,
                              'maxls':15,'finite_diff_rel_step':1e-5})
        status={'status':int(res.status),'message':str(res.message),'success':bool(res.success)}
    except Budget:status={'status':'budget_or_time_stop','success':False}
    record={'label':label,'calls':calls,'elapsed_seconds':time.monotonic()-started,
            'best_adjoint_ratio':best[0],'best_parameters':best[1].tolist(),
            'status':status,'history':history}
    (BASE/'searches'/f'{label}.json').write_text(json.dumps(record,indent=2)+'\n')
    print(label,calls,best[0],status,flush=True)
    return evaluate(knots,decode(best[1]),target,component,label)

def main():
    (BASE/'candidates').mkdir(exist_ok=True);(BASE/'searches').mkdir(exist_ok=True)
    freeze={'created_utc':utc(),'python':sys.version,'executable':sys.executable,
            'numpy':np.__version__,'scipy':scipy.__version__,'platform':platform.platform(),
            'files':{n:hashlib.sha256((BASE/n).read_bytes()).hexdigest()
                     for n in ['protocol.txt','scout_kernel.cpp','scout.py']}}
    (BASE/'pre-run-freeze.json').write_text(json.dumps(freeze,indent=2)+'\n')
    results=[]
    for target,component in itertools.product([2.,4.],[1,2]):
        for r in [80,90,100,110,120]:
            label=f'constant-r{r}-t{int(target)}-c{component}'
            results.append(evaluate(GRID,np.full(len(GRID),r,dtype=float),target,component,label))
        coarse=np.r_[0,np.linspace(target-1,target,21)]
        def decode(p):return np.interp(GRID,coarse,p)
        for k,seed in enumerate([2026101801,2026101802,2026101803]):
            x0=np.full(len(coarse),80. if k==0 else 120.) if k<2 else np.random.default_rng(seed).uniform(80,120,len(coarse))
            label=f'opt-t{int(target)}-c{component}-seed{seed}'
            results.append(optimize_rates(GRID,decode,x0,target,component,1200,label))
    best=max(results,key=lambda r:r['winner']['probe_ratio']);peak=local_peak(best)
    # One predeclared local input-grid refinement, exact microsecond endpoints.
    lo=max(0,peak['target_time']-.25);hi=min(4,peak['target_time']+.05)
    extra=np.arange(round(lo*1e6),round(hi*1e6)+1,2000,dtype=float)/1e6
    knots=np.unique(np.round(np.r_[GRID,extra,lo,hi,peak['target_time']],6))
    base=np.interp(knots,best['knots'],best['rate'])
    indices=np.flatnonzero((knots>=lo-1e-12)&(knots<=hi+1e-12))
    def decode_refined(p):
        r=base.copy();r[indices]=p;return r
    refined=optimize_rates(knots,decode_refined,base[indices],peak['target_time'],peak['component'],3000,'refined')
    results.append(refined)
    final=max(results,key=lambda r:r['winner']['probe_ratio']);finalpeak=local_peak(final)
    frozen={'created_utc':utc(),'label':final['label'],'target':finalpeak,
            'knots':[rational(x) for x in final['knots']],
            'rate':[rational(x) for x in final['rate']],
            'disturbance':[rational(x) for x in final['disturbance']],
            'initial_z':[rational(x) for x in finalpeak['z']],
            'target_time':rational(finalpeak['target_time']),
            'interpolation':'continuous piecewise linear on saved knots',
            'scope':'Numerical candidate, initial cube; not DirectPlant endpoint reachability'}
    (BASE/'frozen-candidate.json').write_text(json.dumps(frozen,indent=2)+'\n')
    summary={'finished_utc':utc(),'candidate_count':len(results),'strongest_before_refinement':best['label'],
             'refinement_peak':peak,'final_label':final['label'],'final_peak':finalpeak,
             'results':[{'label':r['label'],'winner':r['winner']} for r in results]}
    (BASE/'search-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2),flush=True)
if __name__=='__main__':main()
