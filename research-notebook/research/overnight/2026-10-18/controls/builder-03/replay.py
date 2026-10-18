"""Separate DOP853 replay and controls; no import from the search implementation."""
from pathlib import Path
from fractions import Fraction
import datetime, hashlib, itertools, json, sys
import numpy as np
import scipy
from scipy.integrate import solve_ivp
BASE=Path(__file__).resolve().parent
record=json.loads((BASE/'frozen-candidate.json').read_text())
F=lambda s:float(Fraction(s))
knots=np.array(list(map(F,record['knots'])))
rates=np.array(list(map(F,record['rate'])))
dist=np.array(list(map(F,record['disturbance'])))
target=F(record['target_time'])
zlist=[np.array(z)*.0002 for z in itertools.product([-1,1],repeat=3)]+[np.zeros(3)]
def physical(z):return np.array([z[0],40*(z[1]-z[0]),1600*(z[2]-2*z[1]+z[0])])
states=np.array([physical(z)/np.array([1,40,1600]) for z in zlist]).T
times=np.unique(np.r_[np.arange(4001)/1000,target]);out=np.empty((len(times),3,9));out[0]=states
nfev=0
for j,(lo,hi) in enumerate(zip(knots[:-1],knots[1:])):
    def rhs(t,y):
        f=(t-lo)/(hi-lo);r=rates[j]+f*(rates[j+1]-rates[j]);w=dist[j]+f*(dist[j+1]-dist[j])
        Y=y.reshape(3,9);D=np.empty_like(Y)
        D[0]=40*Y[1];D[1]=40*Y[2]
        D[2]=r*(-.5*Y[0]-1.5*Y[1]-1.5*Y[2]+w/1600)
        return D.ravel()
    sol=solve_ivp(rhs,(lo,hi),states.ravel(),method='DOP853',rtol=2e-12,atol=2e-15,dense_output=True)
    if not sol.success:raise RuntimeError(sol.message)
    take=np.flatnonzero((times>lo)&(times<=hi))
    if len(take):out[take]=sol.sol(times[take]).T.reshape(-1,3,9)
    states=sol.y[:,-1].reshape(3,9);nfev+=sol.nfev
rows=[]
for k,z in enumerate(zlist):
    mask=times>=2;vals=np.abs(out[mask,1:,k])*np.array([40000,80000])
    ti,ci=np.unravel_index(vals.argmax(),vals.shape)
    rows.append({'z':z.tolist(),'initial_physical':physical(z).tolist(),
                 'ratio':float(vals[ti,ci]),'time':float(times[mask][ti]),'component':int(ci+1),
                 'max_velocity_mps':float(np.max(np.abs(out[mask,1,k]))*40),
                 'max_acceleration_mps2':float(np.max(np.abs(out[mask,2,k]))*1600),
                 'target_physical':(out[np.where(times==target)[0][0],:,k]*np.array([1,40,1600])).tolist()})
np.savez_compressed(BASE/'dop853-traces.npz',times=times,scaled_states=out,initial_z=np.array(zlist))
np.savetxt(BASE/'dop853-strongest.csv',np.column_stack([times,out[:,:,0]*[1,40,1600]]),
           delimiter=',',header='time_s,position_m,velocity_mps,acceleration_mps2',comments='')

# Controls use the same physical ODE but separate constant schedules.
controls=[]
for r,w,z in [(80.,0.,np.zeros(3)),(120.,0.,np.zeros(3)),
               (80.,.01,np.zeros(3)),(120.,.01,np.zeros(3))]:
    y0=physical(z)
    def rhs(t,y):return [y[1],y[2],r*(-800*y[0]-60*y[1]-1.5*y[2]+w)]
    sol=solve_ivp(rhs,[0,4],y0,method='DOP853',rtol=2e-12,atol=2e-15,t_eval=np.arange(4001)/1000)
    if not sol.success:raise RuntimeError(sol.message)
    controls.append({'r':r,'w':w,'initial_z':z.tolist(),'final_physical':sol.y[:,-1].tolist(),
                     'expected_equilibrium_position':w/800,'max_v_after2':float(np.max(abs(sol.y[1,2000:]))),
                     'max_a_after2':float(np.max(abs(sol.y[2,2000:]))),
                     'zero_control_exact_numeric':bool(np.array_equal(sol.y,np.zeros_like(sol.y))) if w==0 else None})

result={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'method':'Independent SciPy DOP853, split at every continuous input knot',
        'source_hash':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'candidate_sha256':hashlib.sha256((BASE/'frozen-candidate.json').read_bytes()).hexdigest(),
        'python':sys.version,'numpy':np.__version__,'scipy':scipy.__version__,
        'rtol':2e-12,'atol_scaled':2e-15,'nfev':nfev,'vertices':rows,'controls':controls,
        'claim':'Numerical replay only; samples do not certify an all-time bound'}
(BASE/'dop853-replay.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
