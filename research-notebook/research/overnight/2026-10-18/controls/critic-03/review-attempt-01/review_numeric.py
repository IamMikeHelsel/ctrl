#!/usr/bin/env python3
"""Fixed-candidate review only. Does not optimize or alter frozen evidence."""
from pathlib import Path
from fractions import Fraction as Q
import ctypes as ct,hashlib,itertools,json,time
import numpy as np
from scipy.integrate import solve_ivp
HERE=Path(__file__).resolve().parent;SOURCE=HERE.parent/'builder-03'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(SOURCE/'artifact-sha256.json')=='7c270b9f1559b6895434cf238e8bd9500009ce40442b3ce0cc31a2c9d95a29e9'
artifacts=json.loads((SOURCE/'artifact-sha256.json').read_text())
assert all(sha(SOURCE/p)==h for p,h in artifacts.items())
freeze=json.loads((SOURCE/'pre-run-freeze.json').read_text())
assert all(sha(SOURCE/p)==h for p,h in freeze['files'].items())
record=json.loads((SOURCE/'frozen-candidate.json').read_text())
knotsQ=list(map(Q,record['knots']));ratesQ=list(map(Q,record['rate']));wQ=list(map(Q,record['disturbance']))
assert knotsQ[0]==0 and knotsQ[-1]==4 and all(a<b for a,b in zip(knotsQ,knotsQ[1:]))
assert len(knotsQ)==len(ratesQ)==len(wQ)==528
assert all(80<=q<=120 for q in ratesQ) and all(abs(q)<=Q(1,100) for q in wQ)
assert 2<=Q(record['target_time'])<=4
assert all(abs(Q(q))<=Q(1,5000) for q in record['initial_z'])
k=np.array(list(map(float,knotsQ)));r=np.array(list(map(float,ratesQ)));w=np.array(list(map(float,wQ)));T=float(Q(record['target_time']))
vertices=np.array(list(itertools.product([-1,1],repeat=3)),float)/5000
zs=np.vstack([vertices,np.zeros(3)])
physical=np.array([[1,0,0],[-40,40,0],[1600,-3200,1600]],float)
y0=zs@physical.T
times=np.unique(np.r_[np.arange(4001)/1000,T])
states=np.empty((len(times),9,3));states[0]=y0
Y=y0.copy();calls=0;started=time.monotonic()
for j,(lo,hi) in enumerate(zip(k[:-1],k[1:])):
    dr=(r[j+1]-r[j])/(hi-lo);dw=(w[j+1]-w[j])/(hi-lo)
    def ode(t,flat):
        y=flat.reshape(9,3);d=np.empty_like(y);rr=r[j]+dr*(t-lo);ww=w[j]+dw*(t-lo)
        d[:,0]=y[:,1];d[:,1]=y[:,2];d[:,2]=rr*(-800*y[:,0]-60*y[:,1]-1.5*y[:,2]+ww)
        return d.ravel()
    sol=solve_ivp(ode,(lo,hi),Y.ravel(),method='DOP853',rtol=3e-13,atol=np.tile([1e-17,1e-15,1e-13],9),dense_output=True)
    assert sol.success,sol.message
    mask=(times>lo)&(times<=hi);states[mask]=sol.sol(times[mask]).T.reshape(-1,9,3)
    Y=sol.y[:,-1].reshape(9,3);calls+=sol.nfev
targetidx=np.flatnonzero(times==T)[0]
br=json.loads((SOURCE/'dop853-replay.json').read_text())
rows=[]
for i,z in enumerate(zs):
    true=next(a for a in br['vertices'] if np.array_equal(np.array(a['z']),z))
    diff=np.abs(states[targetidx,i]-np.array(true['target_physical']))
    assert max(diff/np.array([1e-12,1e-11,1e-9]))<1,diff
    vals=np.abs(states[times>=2,i,1:])/np.array([.001,.02]);ti,ci=np.unravel_index(vals.argmax(),vals.shape)
    rows.append({'initial_z':z.tolist(),'target_physical':states[targetidx,i].tolist(),'difference_from_builder_physical':diff.tolist(),'sampled_ratio':float(vals[ti,ci]),'sampled_time':float(times[times>=2][ti]),'component':int(ci+1)})
np.savez_compressed(HERE/'independent-physical-traces.npz',times=times,physical=states,initial_z=zs)

# Inspect every stored candidate, vertex score, input bound and optimizer budget.
candidate_records=[]
K=ct.CDLL(str(HERE/'.cache/review_kernel.dylib'))
P=np.ctypeslib.ndpointer(dtype=np.float64,ndim=1,flags='C_CONTIGUOUS')
K.forward.argtypes=[ct.c_int,P,P,P,ct.c_int,P,P,ct.c_double,P]
K.adverse.argtypes=[ct.c_int,P,P,ct.c_double,ct.c_int,ct.c_double,P,P];K.adverse.restype=ct.c_double
arr=lambda x:np.ascontiguousarray(x,dtype=float)
max_summary_error=0;max_seen_v=0;max_seen_a=0
for file in sorted((SOURCE/'candidates').glob('*.json')):
    rec=json.loads(file.read_text());kk=arr(rec['knots']);rr=arr(rec['rate']);ww=arr(rec['disturbance'])
    assert len(kk)==len(rr)==len(ww) and kk[0]==0 and kk[-1]==4 and np.all(np.diff(kk)>0)
    assert all(80<=Q(str(q))<=120 for q in rr) and all(abs(Q(str(q)))<=Q(1,100) for q in ww)
    assert sorted(tuple(q['z']) for q in rec['vertices'])==sorted(tuple(q) for q in zs)
    probe=np.arange(4001,dtype=float)/1000
    for z in zs:
        yy=arr([z[0],z[1]-z[0],z[2]-2*z[1]+z[0]]);out=np.empty(len(probe)*3)
        K.forward(len(kk),kk,rr,ww,len(probe),probe,yy,.001,out)
        out=out.reshape(-1,3);vals=np.abs(out[2000:,1:])*[40000,80000]
        row=next(a for a in rec['vertices'] if np.array_equal(a['z'],z))
        err=abs(float(vals.max())-row['probe_ratio']);max_summary_error=max(max_summary_error,err)
        assert err<1e-11,(file,z,err)
        assert abs(np.max(abs(out[2000:,1]))*40-row['max_v_mps'])<1e-12
        assert abs(np.max(abs(out[2000:,2]))*1600-row['max_a_mps2'])<1e-11
        max_seen_v=max(max_seen_v,row['max_v_mps']);max_seen_a=max(max_seen_a,row['max_a_mps2'])
    candidate_records.append({'label':rec['label'],'vertices_checked':9,'knots':len(kk),'source_sha256':sha(file)})
assert len(candidate_records)==33
searches=[];total=0
for file in sorted((SOURCE/'searches').glob('*.json')):
    rec=json.loads(file.read_text());budget=3000 if rec['label']=='refined' else 1200
    assert rec['calls']==len(rec['history'])<=budget
    assert [v['call'] for v in rec['history']]==list(range(1,rec['calls']+1))
    assert rec['best_adjoint_ratio']==max(v['ratio'] for v in rec['history'])
    total+=rec['calls'];searches.append({'label':rec['label'],'calls':rec['calls'],'status':rec['status']})
assert total==11698 and len(searches)==13

# Independently derived physical-coordinate adjoint for the fixed refined target.
ref=json.loads((SOURCE/'candidates/refined.json').read_text());target=ref['target_time'];component=ref['target_component']
lam=np.zeros(3);lam[component]=1/[None,.001,.02][component];weights=np.zeros(len(k))
for j in reversed(range(len(k)-1)):
    lo,hi=k[j:j+2];top=min(target,hi)
    if lo>=top:continue
    dr=(r[j+1]-r[j])/(hi-lo)
    def adj(t,y):
        rr=r[j]+dr*(t-lo);f=(t-lo)/(hi-lo);a,b,c=y[:3]
        return [800*rr*c,-a+60*rr*c,-b+1.5*rr*c,-rr*c*(1-f),-rr*c*f]
    sol=solve_ivp(adj,(top,lo),np.r_[lam,0.,0.],method='DOP853',rtol=3e-13,atol=1e-15)
    assert sol.success
    lam=sol.y[:3,-1];weights[j:j+2]+=sol.y[3:,-1]
zcoef=physical.T@lam
support=np.sum(abs(zcoef))/5000+np.sum(abs(weights))/100
kw=np.zeros(len(k));kz=np.zeros(3)
kernel_support=K.adverse(len(k),arr(k),arr(r),target,component,.001,kw,kz)
assert abs(kernel_support-support)<2e-6
assert abs(ref['adjoint_ratio']-kernel_support)<1e-10
vertex_support=max(z@zcoef for z in zs)
assert abs(vertex_support-np.sum(abs(zcoef))/5000)<1e-12
prefix=next(json.loads(p.read_text()) for p in (SOURCE/'candidates').glob('opt-t4-c2-*.json') if '2026101803' in p.name)
rateprefix=np.array(prefix['rate'])[:301]
assert not np.allclose(rateprefix,rateprefix[0])
assert np.max(abs(rateprefix-np.linspace(rateprefix[0],rateprefix[-1],301)))<1.1e-6
checks={'original_limit_not_violated_at_target':abs(states[targetidx,0,2])<.02,'diagnostic_0_013_detected':abs(states[targetidx,0,2])>.013,'nonzero_target_velocity':abs(states[targetidx,0,1])>1e-5,'zero_score_is_zero':max(abs(np.zeros(2))/[.001,.02])==0,'disclosed_prefix_is_linear_not_constant':True}
assert all(checks.values())
assert all(sha(SOURCE/p)==h for p,h in artifacts.items())
result={'passed':True,'scope':'limited numerical evidence only; no additional search','builder_artifact_count':len(artifacts),'frozen_source_hashes_match':True,'knots':len(k),'initial_states_replayed':9,'physical_replay_method':'DOP853 on e,v,a, independent physical-coordinate ODE, split every input knot','function_evaluations':calls,'vertices':rows,'all_saved_candidate_scores':candidate_records,'maximum_saved_score_replay_error':max_summary_error,'max_observed_search_velocity_mps':max_seen_v,'max_observed_search_acceleration_mps2':max_seen_a,'searches':searches,'objective_evaluations':total,'adjoint_review':{'target':target,'component':component,'independent_physical_support':float(support),'kernel_support':float(kernel_support),'support_difference':float(abs(kernel_support-support)),'max_weight_difference':float(np.max(abs(weights-kw))),'max_initial_coefficient_difference':float(np.max(abs(zcoef-kz)))},'controls':checks,'candidate_sha256':sha(SOURCE/'frozen-candidate.json'),'seconds':time.monotonic()-started}
(HERE/'numeric-review.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k] for k in ['passed','knots','initial_states_replayed','objective_evaluations','adjoint_review','seconds']},indent=2))
