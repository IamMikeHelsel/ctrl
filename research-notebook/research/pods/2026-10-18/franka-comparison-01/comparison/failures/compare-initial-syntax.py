#!/usr/bin/env python3
"""B1: reproducible sampled-data RG adaptation and C5 policy comparison.
Own derivation in DERIVATION.txt. scipy/numpy floating arithmetic; no validated numerics.
"""
import argparse, hashlib, json, platform, sys, time
from pathlib import Path
import numpy as np
import scipy
from scipy.linalg import expm
from scipy.optimize import brentq

K = np.array([8., 6., .5])
S = np.array([[1.,0,0,0],[1.,.25,0,0],[1.,.5,.0625,0],[8/24,6/24,.5/24,1/24]])
EQ = np.array([1.,0,0,0])


def transition(rate, t):
    P=np.array([[0.,1,0],[0,0,1],[0,0,-rate]])
    M=np.zeros((4,4)); M[:3,:3]=P; M[2,3]=rate
    E=expm(t*M)
    return E[:3,:3],E[:3,3]


def policy_c5(m):
    a=np.array([m[0],m[0]+m[1]/4,m[0]+m[1]/2+m[2]/16])
    E=np.array([101533,368033,1042283])/1e8; w=np.array([1.02,1.01,1.])
    radius=max(.045,np.max((a[:,None]-a[None,:]+E[:,None]+E[None,:])/(w[:,None]+w[None,:])))
    return float(np.max(a+E-w*radius)),float(radius)


def guard_c5(m):
    return m[0] <= .143+1e-12 and abs(m[1]) <= .01122+1e-12 and -1.27-1e-12 <= m[2] <= -.2+1e-12


class Governor:
    def __init__(self, cfg):
        self.cfg=cfg; r=cfg['rate_per_second']; T=cfg['sample_period_seconds']; D=cfg['dispatch_delay_seconds']
        AT,BT=transition(r,T); AD,BD=transition(r,D); AR,BR=transition(r,T-D)
        J=AR@BD
        self.F=np.block([[AT-BR[:,None]*K,J[:,None]],[-K[None,:],np.zeros((1,1))]])
        self.B=np.r_[8*BR,8.]
        self.G=np.column_stack([np.r_[BR,1.],np.r_[J,0.],np.r_[BR,0.]])
        self.H=np.vstack([AT,np.zeros(3)])
        self.G0=np.column_stack([np.r_[J,0.],np.r_[BR,0.]])
        self.sensor=np.array(cfg['sensor_error_bounds'])
        self.nu=np.array([K@self.sensor,cfg['target_error_bound'],cfg['target_error_bound']])
        self.target_error=cfg['target_error_bound']
        self.AT,self.BT,self.AD,self.BD,self.AR,self.BR=AT,BT,AD,BD,AR,BR
        N=cfg['prediction_steps']; self.powers=np.empty((N+1,4,4)); self.powers[0]=np.eye(4)
        for h in range(N): self.powers[h+1]=self.powers[h]@self.F
        rows=[]; coeff=[]; bounds=[]; kinds=[]
        def add(row, c, b, kind):
            rows.append(row); coeff.append(c); bounds.append(b-cfg['numerical_inequality_reserve']); kinds.append(kind)
        def bounded(row,c,lo,hi,error,kind):
            add(row,c,hi-error,kind+' upper'); add(-row,-c,-lo-error,kind+' lower')
        # Generic rows for future cells; each has current local disturbance support.
        profiles=[]
        for j in range(cfg['position_grid_divisions']):
            tau=j*T/cfg['position_grid_divisions']
            A,b=transition(r,tau)
            if tau<=D:
                old=b; new=np.zeros(3)
            else:
                Ar,br=transition(r,tau-D); old=Ar@BD; new=br
            C=np.r_[A[0]-new[0]*K,old[0]]; dc=8*new[0]
            local=(abs(new[0])*self.nu[0]+(abs(old[0])+abs(new[0]))*0 # filled separately
            local=abs(new[0])*self.nu[0]+(abs(old[0])+abs(new[0]))*self.target_error
            profiles.append((C,dc,local,'position',tau,A[0],old[0],new[0]))
        profiles.append((np.array([0.,1,0,0]),0.,0.,'speed',0.,None,None,None))
        profiles.append((np.r_[-K,0.],8.,self.nu[0],'command',0.,None,None,None))
        lim=cfg['position_limits_m']; margin=cfg['position_tightening_m']
        # Current cell: actual command is known from m, so current sensor error
        # must propagate with the OPEN plant matrix, not F (no double counting).
        for C,dc,local,kind,tau,Ar,old,new in profiles:
            if kind=='position':
                er=abs(Ar)@self.sensor+(abs(old)+abs(new))*self.target_error
                bounded(C,dc,lim[0]+margin,lim[1]-margin,er,'first '+kind)
            elif kind=='speed': bounded(C,dc,-cfg['speed_certificate_bound'],cfg['speed_certificate_bound'],self.sensor[1],'first speed')
            else: bounded(C,dc,-2,2,0.,'first command')
        # Later cells, constant proposed reference and arbitrary future errors.
        for C,dc,local,kind,*_ in profiles:
            cumulative=0.
            for h in range(1,N):
                row=C@self.powers[h]
                first=C@self.powers[h-1]
                uncertainty=abs(first@self.H)@self.sensor+abs(first@self.G0).sum()*self.target_error+cumulative+local
                cc=C@EQ+dc-row@EQ
                if kind=='position': bounded(row,cc,lim[0]+margin,lim[1]-margin,uncertainty,kind)
                elif kind=='speed': bounded(row,cc,-cfg['speed_certificate_bound'],cfg['speed_certificate_bound'],uncertainty,kind)
                else: bounded(row,cc,-2,2,uncertainty,kind)
                cumulative+=abs(C@self.powers[h-1]@self.G)@self.nu
        # Terminal B-box in transformed equilibrium coordinates at step N.
        for C in S:
            first=C@self.powers[N-1]
            uncertainty=abs(first@self.H)@self.sensor+abs(first@self.G0).sum()*self.target_error
            uncertainty+=sum(abs(C@self.powers[i]@self.G)@self.nu for i in range(N-1))
            row=C@self.powers[N]
            bounded(row,-row@EQ,-cfg['terminal_radius'],cfg['terminal_radius'],uncertainty,'terminal')
        self.rows=np.array(rows); self.coeff=np.array(coeff); self.bounds=np.array(bounds); self.kinds=kinds
        self.pos=self.coeff>1e-13; self.neg=self.coeff< -1e-13; self.flat=~(self.pos|self.neg)
        self.tail=self.tail_check()

    def interval(self,m,old):
        x=np.r_[m,old]
        remainder=self.bounds-np.einsum('ij,j->i',self.rows,x)
        lo,hi=self.cfg['reference_interval_m']
        if np.any(remainder[self.flat]<0):
            return None,{'reason':'flat constraint','min_slack':float(remainder[self.flat].min())}
        hi=min(hi,float(np.min(remainder[self.pos]/self.coeff[self.pos])))
        lo=max(lo,float(np.max(remainder[self.neg]/self.coeff[self.neg])))
        if lo>hi: return None,{'reason':'empty reference interval','lo':lo,'hi':hi}
        return (lo,hi),None

    def tail_check(self):
        cfg=self.cfg; A=S@self.F@np.linalg.inv(S); G=S@self.G
        power=np.eye(4); cumulative=np.zeros(4); worst=np.zeros(4)
        B=cfg['terminal_radius']; m=cfg['terminal_block_steps']
        for i in range(m):
            worst=np.maximum(worst,abs(power).sum(axis=1)*B+cumulative)
            cumulative+=abs(power@G)@self.nu; power=power@A
        endpoint=abs(power).sum(axis=1)*B+cumulative
        box=worst
        speed=4*(box[0]+box[1]); acceleration=16*(box[0]+2*box[1]+box[2])
        command=8*sum(box[:3])+self.nu[0]
        xlo,xhi=cfg['reference_interval_m']; margin=cfg['position_tightening_m']
        checks={
            'block_maps_box_strictly_inside':bool(np.all(endpoint<B-1e-10)),
            'terminal_speed_less_certificate_bound':bool(speed<cfg['speed_certificate_bound']),
            'terminal_acceleration_less_2p01':bool(acceleration<2.01),
            'terminal_unclipped_command_less_2':bool(command<2),
            'terminal_position_upper':bool(xhi+box[0]+margin<cfg['position_limits_m'][1]),
            'terminal_position_lower':bool(xlo-box[0]-margin>cfg['position_limits_m'][0]),
            'intersample_tightening':bool(margin>(cfg['speed_certificate_bound']+2.01*cfg['sample_period_seconds'])*cfg['sample_period_seconds']/cfg['position_grid_divisions']),
            'sampled_closed_loop_schur':bool(max(abs(np.linalg.eigvals(self.F)))<1),
            'equilibrium_identity':bool(np.max(abs(self.F@EQ+self.B-EQ))<1e-12),
        }
        return dict(checks=checks, endpoint_box=endpoint.tolist(), phase_box=box.tolist(),speed=speed,acceleration=acceleration,command=command,
                    eigenvalues=[[float(z.real),float(z.imag)] for z in np.linalg.eigvals(self.F)],
                    block_norm_inf=float(np.linalg.norm(power,np.inf)),F=self.F.tolist(),B=self.B.tolist(),G=self.G.tolist(),S=S.tolist(),
                    note='Binary64 checks of a written block-invariance construction, not interval-certified or Lean proof.')


def pattern(k,name,cfg):
    if name=='zero': sign=0
    elif name=='positive_drive': sign=1
    elif name=='negative_drive': sign=-1
    elif name=='alternating': sign=1 if (k//25)%2==0 else -1
    else: raise ValueError(name)
    return -sign*np.array(cfg['sensor_error_bounds']),sign*cfg['target_error_bound']


def segment(s,u,d,r,h):
    """Physical exact constant-input flow; extrema of x from v=0 on the segment.
    a(t)=u+d+(a0-u-d)exp(-rt), so v' has at most one zero;
    split v at that zero to bracket every v-root, including a double root.
    """
    target=u+d
    def state(t):
        z=np.exp(-r*t); da=s[2]-target
        return np.array([s[0]+s[1]*t+target*t*t/2+da*(t/r-(1-z)/r**2),
                         s[1]+target*t+da*(1-z)/r,target+da*z])
    times=[0.,h]; da=s[2]-target
    if da!=0 and 0 < -target/da < 1:
        tc=-np.log(-target/da)/r
        if 0<tc<h: times.append(float(tc))
    brackets=sorted(times)
    for a,b in zip(brackets[:-1],brackets[1:]):
        va,vb=state(a)[1],state(b)[1]
        if va*vb<0: times.append(float(brentq(lambda t:state(t)[1],a,b,xtol=1e-14)))
    vals=[state(t) for t in times]
    return state(h),min(z[0] for z in vals),max(z[0] for z in vals)


def run_case(cfg,gov,case,name,controller,trace_path):
    T=cfg['sample_period_seconds']; D=cfg['dispatch_delay_seconds']; r=cfg['rate_per_second']; n=round(cfg['horizon_seconds']/T)
    m0=np.array(case['measurement']); s=m0-np.array(case['initial_sensor_error']); old=cfg['pending_command_m_per_s2']
    assert guard_c5(m0) and abs(s[2])<=2.01
    c5,K5=policy_c5(m0); last_ref=None; fallbacks=0; fails=[]; min_slack=float('inf'); trajectory=[]
    minx=maxx=float(s[0]); initial=float(s[0]); command_peak=abs(old); intabs=0.; intsq=0.; tv=0.; saturation=0
    target=cfg['requested_position_m']; start=time.perf_counter(); ref_first=None
    for k in range(n):
        e,d=pattern(k,name,cfg)
        m=m0 if k==0 else s+e
        if controller=='C5': c=c5
        else:
            feasible,reason=gov.interval(m,old)
            if feasible is None:
                if last_ref is None: raise RuntimeError(f'No initial admissible reference {case["id"]} {name}: {reason}')
                c=last_ref; fallbacks+=1
                if len(fails)<5: fails.append({'sample':k,**reason})
            else:
                c=float(np.clip(target,*feasible)); last_ref=c
                slack=gov.bounds-gov.rows@np.r_[m,old]-gov.coeff*c
                min_slack=min(min_slack,float(slack.min()))
        raw=8*c-K@m; u=float(np.clip(raw,-2,2)); saturation+=int(abs(raw-u)>1e-12)
        if ref_first is None: ref_first=c
        trajectory.append((k*T,*s,*m,old,u,c,d))
        s1,mn,mx=segment(s,old,d,r,D); minx=min(minx,mn);maxx=max(maxx,mx)
        s,mn,mx=segment(s1,u,d,r,T-D); minx=min(minx,mn);maxx=max(maxx,mx)
        intabs+=abs(old)*D+abs(u)*(T-D); intsq+=old**2*D+u**2*(T-D);tv+=abs(u-old)
        command_peak=max(command_peak,abs(u)); old=u
    np.savetxt(trace_path,np.array(trajectory),delimiter=',',header='time,x,v,a,mx,mv,ma,old_command,new_command,internal_reference,target_error',comments='',fmt='%.12g')
    return dict(case=case['id'],pattern=name,controller=controller,initial_state=(m0-np.array(case['initial_sensor_error'])).tolist(),
                requested_position=target,internal_reference_first=ref_first,internal_reference_final=c,policy_radius=K5 if controller=='C5' else None,
                final_state=s.tolist(),final_target_error=float(s[0]-target),absolute_final_target_error=float(abs(s[0]-target)),
                peak_position=maxx,minimum_position=minx,forward_travel=maxx-initial,retreat=initial-minx,recovery_from_lowest=float(s[0]-minx),
                forward_margin=cfg['position_limits_m'][1]-maxx,lower_margin=minx-cfg['position_limits_m'][0],command_peak=command_peak,
                integral_absolute_command=intabs,integral_squared_command=intsq,command_total_variation=tv,clip_count=saturation,
                fallback_count=fallbacks,fallback_examples=fails,minimum_accepted_plan_slack=min_slack if controller=='RG' else None,
                elapsed_seconds=time.perf_counter()-start,trace=trace_path.name,
                guarantee='Executed binary64 piecewise-exponential trajectory with numerical extremum location; not a robust/all-time certificate.')


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--input',type=Path,default=Path(__file__).with_name('inputs.json'));ap.add_argument('--output',type=Path,required=True);ap.add_argument('--quick',action='store_true'); args=ap.parse_args()
    cfg=json.loads(args.input.read_text()); args.output.mkdir(parents=True,exist_ok=False)
    t=time.perf_counter(); gov=Governor(cfg)
    assert all(gov.tail['checks'].values()),gov.tail
    (args.output/'model-and-tail.json').write_text(json.dumps(gov.tail,indent=2)+'\n')
    results=[]
    cases=cfg['initial_cases'][:1] if args.quick else cfg['initial_cases']; patterns=cfg['patterns'][:1] if args.quick else cfg['patterns']
    for case in cases:
      for name in patterns:
       for controller in ['C5','RG']:
        trace=args.output/f'{case["id"]}-{name}-{controller}.csv'
        result=run_case(cfg,gov,case,name,controller,trace);results.append(result)
        print(case['id'],name,controller,'peak',result['peak_position'],'retreat',result['retreat'],'error',result['final_target_error'],'fallback',result['fallback_count'],flush=True)
    summary={'config_sha256':hashlib.sha256(args.input.read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             'python':sys.version,'numpy':np.__version__,'scipy':scipy.__version__,'platform':platform.platform(),'constraint_rows':len(gov.bounds),'elapsed_seconds':time.perf_counter()-t,
             'results':results,'scope':cfg['scope']}
    (args.output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')

if __name__=='__main__': main()
