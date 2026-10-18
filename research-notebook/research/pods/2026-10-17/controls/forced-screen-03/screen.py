#!/usr/bin/env python3
"""The fixed 48-case gate. Exact segment formulas, evaluated by SciPy expm."""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
import csv,json,sys,platform,time
import numpy as np
import scipy
from scipy.linalg import expm
HERE=Path(__file__).resolve().parent
SIGMA=10;DT=F(1,2000);R=F(1,5000)
CONTROLLERS={'original':F(5,48),'lag_compensated_changed':F(29,48)}
RATES={'r80':80,'r100':100,'r120':120,'r80_120_80':None}
DISTURBANCES={'w0':F(0),'wplus':F(1,100),'wminus':F(-1,100)}
JERKS=['plus_to_half','plus_minus_zero']
FIELDS=['t_s','event_side','segment','r_per_s','w_m_per_s2','reference_jerk_m_per_s3','ex_m','ev_m_per_s','ea_m_per_s2','b_m_per_s2','q0_m','q1_m_per_s','q2_m_per_s2','x_m','v_m_per_s','a_m_per_s2','u_m_per_s2','u_star_m_per_s2','u_prime_m_per_s3','actual_jerk_m_per_s3']
METRICS=['ex_m','actual_jerk_m_per_s3','u_m_per_s2','u_star_m_per_s2','u_prime_m_per_s3']
@lru_cache(None)
def A(rho):return np.array([[0,1,0,0],[0,0,1,0],[0,0,-rho,rho],[-16,-12,-1,-2]],float)
@lru_cache(None)
def E(rho,ticks):return expm(A(rho)*float(SIGMA*DT*ticks))
def rate_at(case,t):return RATES[case] if RATES[case] is not None else (120 if F(1,8)<=t<F(3,8) else 80)
def jerk_at(case,t):return 10 if case=='plus_to_half' or t<F(1,4) else (-10 if t<F(1,2) else 0)
def reference_advance(q,j,dt):return [q[0]+q[1]*dt+q[2]*dt*dt/2+j*dt**3/6,q[1]+q[2]*dt+j*dt*dt/2,q[2]+j*dt]
def equilibrium(rho,w,j,k):return [(w+(k-1/rho-F(1,2))*j)/8,F(0),F(0),j/rho-w]
def residual(x,rho,w,j,k):
 return [x[1],x[2],-rho*x[2]+rho*x[3]+rho*w-j,-16*x[0]-12*x[1]-x[2]-2*x[3]+(2*k-1)*j]
def output(t,side,si,r,w,j,k,xi,q):
 ex,ev,ea,b=xi*np.array([1,10,100,100]);q0,q1,q2=map(float,q)
 u=q2+b;us=q2-800*ex-60*ev-ea/2+float(k)*j/10
 return dict(zip(FIELDS,[float(t),side,si,r,float(w),j,ex,ev,ea,b,q0,q1,q2,q0+ex,q1+ev,q2+ea,u,us,20*(us-u),r*(u+float(w)-q2-ea)]))
def main():
 start=time.monotonic();(HERE/'traces').mkdir(exist_ok=True)
 cases=[];checks=[];equilibria=[]
 for controller,k in CONTROLLERS.items():
  for rc in RATES:
   for wc,w in DISTURBANCES.items():
    for jc in JERKS:
     name=f'{controller}__{rc}__{wc}__{jc}';H=F(1,2)if jc=='plus_to_half'else F(1)
     breaks=sorted(set([F(0),H]+([F(1,8),F(3,8)]if rc=='r80_120_80'else[])+([F(1,4),F(1,2)]if jc=='plus_minus_zero'else[])))
     xi=np.zeros(4);q=[F(0)]*3;rows=[];segments=[];crossings=[]
     for si,(t0,t1) in enumerate(zip(breaks,breaks[1:])):
      r=rate_at(rc,t0);j=jerk_at(jc,t0);rho=F(r,SIGMA);wn=w/100;jn=F(j,1000)
      eq=equilibrium(rho,wn,jn,k);assert residual(eq,rho,wn,jn,k)==[0]*4
      equilibria.append({'case':name,'segment':si,'rho':str(rho),'w_normalized':str(wn),'j_normalized':str(jn),'kappa':str(k),'xi_equilibrium':[str(v)for v in eq],'exact_residual_zero':True})
      eqf=np.array(list(map(float,eq)));n=int((t1-t0)/DT);assert n*DT==t1-t0
      seg={'index':si,'t0':str(t0),'t1':str(t1),'r_physical':r,'w_physical':str(w),'j_physical':j,'kappa':str(k),'xi0':xi.tolist(),'q0':[str(v)for v in q]}
      segments.append(seg)
      for m in range(n+1):
       t=t0+m*DT;at=eqf+E(float(rho),m)@(xi-eqf);qt=reference_advance(q,F(j),m*DT)
       side='right'if m==0 and si>0 else ('left'if m==n and t1<H else 'regular')
       row=output(t,side,si,r,w,j,k,at,qt);rows.append(row)
       if len(rows)>1 and rows[-2]['t_s']<row['t_s']:
        a=abs(rows[-2]['ex_m'])-float(R);b=abs(row['ex_m'])-float(R)
        if (a<=0<b)or(b<=0<a):crossings.append({'direction':'exit'if b>0 else 'enter','t_lo_s':rows[-2]['t_s'],'t_hi_s':row['t_s'],'abs_error_lo_m':abs(rows[-2]['ex_m']),'abs_error_hi_m':abs(row['ex_m']),'type':'numerical adjacent-sample threshold bracket'})
      if si>0:
       left=rows[-n-2];right=rows[-n-1]
       vals=['ex_m','ev_m_per_s','ea_m_per_s2','b_m_per_s2','q0_m','q1_m_per_s','q2_m_per_s2','x_m','v_m_per_s','a_m_per_s2','u_m_per_s2']
       diffs={key:right[key]-left[key]for key in vals}
       err=max(map(abs,diffs.values()));assert err<1e-12
       dj=right['reference_jerk_m_per_s3']-left['reference_jerk_m_per_s3']
       jump_expected=float(k)*dj/10
       target_res=(right['u_star_m_per_s2']-left['u_star_m_per_s2'])-jump_expected
       jerk_expected=(right['r_per_s']-left['r_per_s'])*(left['u_m_per_s2']+float(w)-left['a_m_per_s2'])
       jerk_res=right['actual_jerk_m_per_s3']-left['actual_jerk_m_per_s3']-jerk_expected
       assert abs(target_res)<1e-12 and abs(jerk_res)<1e-12
       checks.append({'case':name,'time_s':float(t0),'coordinate_jump_max_abs':err,'continuous_variables':vals,'u_star_jump_residual':target_res,'actual_jerk_jump_residual':jerk_res,'u_star_jump':right['u_star_m_per_s2']-left['u_star_m_per_s2'],'u_prime_jump':right['u_prime_m_per_s3']-left['u_prime_m_per_s3'],'actual_jerk_jump':right['actual_jerk_m_per_s3']-left['actual_jerk_m_per_s3']})
      xi=eqf+E(float(rho),n)@(xi-eqf);q=reference_advance(q,F(j),t1-t0)
     with (HERE/'traces'/f'{name}.csv').open('w',newline='')as f:
      writer=csv.DictWriter(f,fieldnames=FIELDS);writer.writeheader();writer.writerows(rows)
     peaks={key:{'max_abs':abs((row:=max(rows,key=lambda z:abs(z[key])))[key]),'signed_value':row[key],'time_s':row['t_s'],'side':row['event_side'],'segment':row['segment'],'kind':'sampled peak, including both event sides'}for key in METRICS}
     cases.append({'case':name,'controller':controller,'rate_case':rc,'disturbance_case':wc,'jerk_case':jc,'duration_s':float(H),'sample_count':len(rows),'sample_step_s':float(DT),'within_position_target_at_samples':bool(peaks['ex_m']['max_abs']<=float(R)),'peaks':peaks,'crossing_brackets':crossings,'segments':segments,'trace':f'traces/{name}.csv'})
 assert len(cases)==48
 report={'passed_model_checks':True,'case_count':48,'sigma':10,'filter_rate_normalized':2,'filter_rate_physical_per_s':20,'target_radius_m':str(R),'initial_xi':['0']*4,'initial_reference':['0']*3,'reference_origin_assumption':'q0=q1=q2=0 initially; actual states match and u=q2=0. This fixes absolute u and u_star, which xi(0)=0 alone does not fix.','grid_step_s':str(DT),'propagation':'xi=xi_eq+expm(A(rho)*Delta_tau)*(xi0-xi_eq), independently applied from each segment start; analytical exact constant-segment formula evaluated in IEEE float64.','peak_scope':'sampled only, with one-sided event values; no between-sample safety certificate','cases':cases,'seconds':time.monotonic()-start}
 (HERE/'screen-result.json').write_text(json.dumps(report,indent=2)+'\n')
 (HERE/'continuity-checks.json').write_text(json.dumps({'passed':True,'checks':checks},indent=2)+'\n')
 (HERE/'equilibrium-checks.json').write_text(json.dumps({'passed':True,'arithmetic':'Fraction exact rationals','checks':equilibria},indent=2)+'\n')
 (HERE/'runtime.json').write_text(json.dumps({'python':sys.version,'platform':platform.platform(),'numpy':np.__version__,'scipy':scipy.__version__,'new_installs':False},indent=2)+'\n')
 summary=[]
 for c in cases:
  out={k:c[k]for k in ['case','controller','rate_case','disturbance_case','jerk_case','within_position_target_at_samples']}
  for key,p in c['peaks'].items():out[key+'_sampled_max_abs']=p['max_abs'];out[key+'_peak_time_s']=p['time_s']
  out['first_exit_lo_s']=next((b['t_lo_s']for b in c['crossing_brackets']if b['direction']=='exit'),'')
  out['first_exit_hi_s']=next((b['t_hi_s']for b in c['crossing_brackets']if b['direction']=='exit'),'')
  summary.append(out)
 with (HERE/'summary.csv').open('w',newline='')as f:
  writer=csv.DictWriter(f,fieldnames=list(summary[0]));writer.writeheader();writer.writerows(summary)
 print(json.dumps({'cases':48,'seconds':report['seconds'],'controllers':{c:{'samples_pass':sum(v['within_position_target_at_samples']for v in cases if v['controller']==c),'worst_sampled_error_mm':1000*max(v['peaks']['ex_m']['max_abs']for v in cases if v['controller']==c)}for c in CONTROLLERS}},indent=2))
if __name__=='__main__':main()
