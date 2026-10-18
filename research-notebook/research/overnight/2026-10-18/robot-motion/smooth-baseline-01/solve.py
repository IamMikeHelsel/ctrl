from pathlib import Path
from fractions import Fraction as F
from datetime import datetime, timezone
import hashlib, json, time, warnings
import cvxpy as cp
import numpy as np
import scipy, clarabel

HERE = Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def write(name, value): (HERE/name).write_text(json.dumps(value,indent=2)+'\n')
def now(): return datetime.now(timezone.utc).isoformat()

def propagate(js,dt,initial):
    q,v,a = initial; states=[(q,v,a)]
    for left,right in zip(js,js[1:]):
        q,v,a = (q+dt*v+dt**2*a/2+dt**3*(left/8+right/24),
                 v+dt*a+dt**2*(left/3+right/6), a+dt*(left+right)/2)
        states.append((q,v,a))
    return states

def linear_solve(matrix,rhs):
    rows=[list(row)+[value] for row,value in zip(matrix,rhs)]
    for k in range(3):
        pivot=next(i for i in range(k,3) if rows[i][k])
        rows[k],rows[pivot]=rows[pivot],rows[k]
        divisor=rows[k][k];rows[k]=[x/divisor for x in rows[k]]
        for i in range(3):
            if i!=k:
                scale=rows[i][k];rows[i]=[x-scale*y for x,y in zip(rows[i],rows[k])]
    return [rows[k][3] for k in range(3)]

def exact_objective(js,dt):
    return sum((dt*(a*a+a*b+b*b)/3 for a,b in zip(js,js[1:])),F(0))

def validate(js,dt,initial,cap):
    states=propagate(js,dt,initial); extrema={'speed':F(0),'acceleration':F(0),'jerk':F(0),'snap':F(0)}
    upper=initial[0]+cap;max_position=initial[0]; violations=[]
    controls=[]
    for i,((q,v,a),(qn,vn,an)) in enumerate(zip(states,states[1:])):
        ji,jk=js[i:i+2]
        qb=[q,q+dt*v/4,q+dt*v/2+dt**2*a/12,q+3*dt*v/4+dt**2*a/4+dt**3*ji/24,qn]
        vb=[v,v+dt*a/3,v+2*dt*a/3+dt**2*ji/6,vn]
        ab=[a,a+dt*ji/2,an]
        for name,values,limit in [('speed',vb,F(1,10)),('acceleration',ab,F(1,2)),('jerk',[ji,jk],F(15,2))]:
            extrema[name]=max(extrema[name],*(abs(x) for x in values))
            if any(abs(x)>limit for x in values):violations.append({'cell':i,'condition':name})
        if max(qb)>upper:violations.append({'cell':i,'condition':'position_cap'})
        max_position=max(max_position,*qb);extrema['snap']=max(extrema['snap'],abs((jk-ji)/dt))
        controls.append({'cell':i,'q':list(map(str,qb)),'v':list(map(str,vb)),'a':list(map(str,ab))})
    if states[-1]!=(0,0,0):violations.append({'condition':'terminal_state'})
    if js[0]!=F(-5,4) or js[-1]!=0:violations.append({'condition':'terminal_or_initial_jerk'})
    return {'passed':not violations,'violations':violations,'bernstein_absolute_bounds':{k:str(v) for k,v in extrema.items()},
            'reference_forward_excursion_upper_bound_m':str(max_position-initial[0]),'terminal_state':list(map(str,states[-1])),
            'controls':controls},states

def one(n,cap,config):
    label=f'n{n}_cap{int(cap*1000)}mm';dt=F(9,10*n);h=float(dt)
    initial=list(map(F,config['initial_qvaj']));q=cp.Variable(n+1);v=cp.Variable(n+1);a=cp.Variable(n+1);j=cp.Variable(n+1)
    bound_v=(.1-1e-7)*1000;bound_a=(.5-1e-7)*1000;bound_j=(7.5-1e-4)*1000
    upper=(float(initial[0]+cap)-1e-8)*1000
    conditions=[q[0]==float(initial[0])*1000,v[0]==float(initial[1])*1000,a[0]==float(initial[2])*1000,
                j[0]==-1250,j[-1]==0,q[-1]==0,v[-1]==0,a[-1]==0,
                a[1:]==a[:-1]+h*(j[:-1]+j[1:])/2,
                v[1:]==v[:-1]+h*a[:-1]+h*h*(j[:-1]/3+j[1:]/6),
                q[1:]==q[:-1]+h*v[:-1]+h*h*a[:-1]/2+h**3*(j[:-1]/8+j[1:]/24),
                cp.abs(j)<=bound_j,cp.abs(a)<=bound_a,cp.abs(a[:-1]+h*j[:-1]/2)<=bound_a,
                cp.abs(v)<=bound_v,cp.abs(v[:-1]+h*a[:-1]/3)<=bound_v,
                cp.abs(v[:-1]+2*h*a[:-1]/3+h*h*j[:-1]/6)<=bound_v,
                q<=upper,q[:-1]+h*v[:-1]/4<=upper,
                q[:-1]+h*v[:-1]/2+h*h*a[:-1]/12<=upper,
                q[:-1]+3*h*v[:-1]/4+h*h*a[:-1]/4+h**3*j[:-1]/24<=upper]
    jl=j[:-1]/7500;jr=j[1:]/7500
    objective=h/6*(cp.sum_squares(jl+jr)+cp.sum_squares(jl)+cp.sum_squares(jr))
    problem=cp.Problem(cp.Minimize(objective),conditions)
    result={'case':label,'N':n,'cap_m':str(cap),'dt_s':str(dt),'started_utc':now(),'accepted':False}
    start=time.monotonic()
    try:
        with warnings.catch_warnings(record=True) as caught:
            warnings.simplefilter('always')
            problem.solve(solver='CLARABEL',max_iter=config['max_iter'],tol_gap_abs=config['tol_gap_abs'],
                          tol_gap_rel=config['tol_gap_rel'],tol_feas=config['tol_feas'])
        result.update(solver_status=problem.status,solver_warnings=[str(x.message) for x in caught],
                      normalized_objective=problem.value,solver_time_s=problem.solver_stats.solve_time,
                      iterations=problem.solver_stats.num_iters)
        if problem.status=='optimal':
            result['solver_state_mm']={name:variable.value.tolist() for name,variable in [('q',q),('v',v),('a',a),('j',j)]}
            result['max_solver_constraint_violation_mm_units']=max(float(np.max(c.violation())) for c in conditions)
            denominator=config['jerk_rounding_denominator']
            raw=[F(round(float(x)/1000*denominator),denominator) for x in j.value]
            raw[0]=initial[3];raw[-1]=F(0)
            before=propagate(raw,dt,initial[:3])[-1]
            columns=[]
            for index in [n-3,n-2,n-1]:
                impulse=[F(0)]*(n+1);impulse[index]=F(1)
                columns.append(propagate(impulse,dt,[F(0)]*3)[-1])
            correction=linear_solve([[columns[col][row] for col in range(3)] for row in range(3)],[-x for x in before])
            exact=list(raw)
            for index,delta in zip([n-3,n-2,n-1],correction):exact[index]+=delta
            check,states=validate(exact,dt,initial[:3],cap)
            result.update(rounded_jerk_nodes_SI=list(map(str,raw)),corrected_jerk_nodes_SI=list(map(str,exact)),
                          endpoint_before_correction=list(map(str,before)),last_three_corrections=list(map(str,correction)),
                          rounded_reference_jerk_integral_SI=str(exact_objective(raw,dt)),
                          corrected_reference_jerk_integral_SI=str(exact_objective(exact,dt)),validation=check,
                          exact_states_SI=[list(map(str,row)) for row in states],accepted=check['passed'])
    except Exception as error:
        result['error']=repr(error)
    result['elapsed_s']=time.monotonic()-start;result['finished_utc']=now()
    write(label+'.json',result)
    print(label,result.get('solver_status'),result['accepted'],result.get('validation',{}).get('violations'),flush=True)
    return {k:result[k] for k in ['case','N','cap_m','accepted','elapsed_s']}|{'solver_status':result.get('solver_status'),'error':result.get('error')}

def main():
    assert not (HERE/'solver-summary.json').exists(), 'Do not overwrite a solver batch.'
    for manifest in ['protocol-freeze.json','implementation-freeze.json']:
        for name,digest in json.loads((HERE/manifest).read_text())['files'].items():assert sha(HERE/name)==digest,name
    config=json.loads((HERE/'configuration.json').read_text())
    assert (cp.__version__,clarabel.__version__,np.__version__,scipy.__version__)==('1.9.3','0.11.1','2.3.4','1.16.2')
    results=[]
    for n in [config['N_primary'],config['N_refinement']]:
        for cap in map(F,config['caps_m']):results.append(one(n,cap,config))
    write('solver-summary.json',{'finished_utc':now(),'cases':results})

if __name__=='__main__':main()
