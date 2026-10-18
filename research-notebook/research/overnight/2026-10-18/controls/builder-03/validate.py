"""Exact input checks and independent constant-coefficient sensitivity controls."""
from pathlib import Path
from fractions import Fraction as Q
import ctypes as ct, hashlib, json
import numpy as np
from scipy.linalg import expm
BASE=Path(__file__).resolve().parent
record=json.loads((BASE/'frozen-candidate.json').read_text())
knots=list(map(Q,record['knots']));rate=list(map(Q,record['rate']));w=list(map(Q,record['disturbance']))
checks={
    'domain_exact':knots[0]==0 and knots[-1]==4,
    'strict_order_exact':all(a<b for a,b in zip(knots,knots[1:])),
    'rate_bound_exact':all(80<=r<=120 for r in rate),
    'disturbance_bound_exact':all(abs(v)<=Q(1,100) for v in w),
    'initial_cube_exact':all(abs(Q(v))<=Q(1,5000) for v in record['initial_z']),
    'target_interval_exact':2<=Q(record['target_time'])<=4,
    'equal_array_lengths':len(knots)==len(rate)==len(w),
    'continuous_interpolation_declared':record['interpolation']=='continuous piecewise linear on saved knots',
}
assert all(checks.values()),checks
K=ct.CDLL(str(BASE/'.cache/scout_kernel.dylib'))
P=np.ctypeslib.ndpointer(dtype=np.float64,ndim=1,flags='C_CONTIGUOUS')
K.adverse.argtypes=[ct.c_int,P,P,ct.c_double,ct.c_int,ct.c_double,P,P];K.adverse.restype=ct.c_double
controls=[]
grid=np.arange(401)/100
transform=np.array([[1,0,0],[-1,1,0],[1,-2,1]])
for r in [80.,100.,120.]:
    A=np.array([[0,40,0],[0,0,40],[-r/2,-3*r/2,-3*r/2]])
    M=np.zeros((5,5));M[:3,:3]=A;M[2,3]=r/1600;M[3,4]=1
    E=expm(M*.01);F=E[:3,:3];g0=E[:3,3]-E[:3,4]/.01;g1=E[:3,4]/.01
    for t in [2.,4.]:
      for c in [1,2]:
        lam=np.zeros(3);lam[c]=40000 if c==1 else 80000;exactweights=np.zeros(401)
        for j in reversed(range(round(t*100))):
            exactweights[j]+=lam@g0;exactweights[j+1]+=lam@g1;lam=F.T@lam
        exactcoefs=transform.T@lam
        support=.0002*np.sum(abs(exactcoefs))+.01*np.sum(abs(exactweights))
        errors=[]
        for step in [.001,.0005]:
            weights=np.zeros(401);coefs=np.zeros(3)
            v=K.adverse(401,grid,np.full(401,r),t,c,step,weights,coefs)
            errors.append({'step':step,'ratio_error':float(abs(v-support)),
                           'weight_max_error':float(np.max(abs(weights-exactweights))),
                           'initial_coefficient_max_error':float(np.max(abs(coefs-exactcoefs)))})
        controls.append({'rate':r,'target':t,'component':c,'matrix_exp_support':float(support),'errors':errors})
        assert errors[0]['ratio_error']<2e-6
        assert errors[1]['ratio_error']<errors[0]['ratio_error']

hp=json.loads((BASE/'high-precision-replay.json').read_text());dp=json.loads((BASE/'dop853-replay.json').read_text())
match=next(v for v in dp['vertices'] if all(Q(str(x))==Q(s) for x,s in zip(v['z'],record['initial_z'])))
delta=[abs(float(a)-b) for a,b in zip(hp['physical_state'],match['target_physical'])]
assert delta[0]<1e-12 and delta[1]<1e-11 and delta[2]<1e-9
negative_controls={
    'exact_rest_is_false':abs(float(hp['physical_state'][1]))>1e-5,
    'diagnostic_acceleration_limit_0_013_is_violated':float(hp['physical_state'][2])>.013,
    'original_acceleration_limit_0_02_not_violated_at_target':abs(float(hp['physical_state'][2]))<.02,
}
assert all(negative_controls.values())
result={'input_checks':checks,'constant_rate_adjoint_controls':controls,
        'dop853_vs_high_precision_absolute_physical_difference':delta,
        'negative_controls':negative_controls,
        'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'note':'Diagnostic 0.013 control tests detection only. It does not replace the frozen 0.02 target.'}
(BASE/'validation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
