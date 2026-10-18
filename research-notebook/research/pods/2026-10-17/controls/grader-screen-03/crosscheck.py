#!/usr/bin/env python3
"""Independent 80-digit Taylor exponential propagation of every saved sample.
Use the existing .tools/research-python runtime (mpmath 1.3.0).
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
import csv,json,time,sys,mpmath as mp
HERE=Path(__file__).resolve().parent
mp.mp.dps=80
DT=mp.mpf(1)/2000;SIGMA=mp.mpf(10);TOL=mp.mpf('2e-10');R=mp.mpf(1)/5000
METRICS=['ex_m','actual_jerk_m_per_s3','u_m_per_s2','u_star_m_per_s2','u_prime_m_per_s3']
FIELDS=['ex_m','ev_m_per_s','ea_m_per_s2','b_m_per_s2','q0_m','q1_m_per_s','q2_m_per_s2','x_m','v_m_per_s','a_m_per_s2','u_m_per_s2','u_star_m_per_s2','u_prime_m_per_s3','actual_jerk_m_per_s3']
def M(x):
 f=F(x);return mp.mpf(f.numerator)/f.denominator
@lru_cache(None)
def step(r,w,j,k):
 rho=mp.mpf(r)/10;wn=M(w)/100;jn=mp.mpf(j)/1000;kap=M(k)
 B=mp.matrix([[0,1,0,0,0],[0,0,1,0,0],[0,0,-rho,rho,rho*wn-jn],[-16,-12,-1,-2,(2*kap-1)*jn],[0,0,0,0,0]])
 return mp.expm(B*(SIGMA*DT),method='taylor')
def output(y,q,j,k,r,w):
 ex=y[0];ev=10*y[1];ea=100*y[2];b=100*y[3]
 u=q[2]+b;ustar=q[2]-800*ex-60*ev-ea/2+M(k)*j/10
 return dict(zip(FIELDS,[ex,ev,ea,b,q[0],q[1],q[2],q[0]+ex,q[1]+ev,q[2]+ea,u,ustar,20*(ustar-u),r*(b+M(w)-ea)]))
def main():
 started=time.monotonic();source=json.loads((HERE/'screen-result.json').read_text());cases=[];globalworst={f:{'max_abs_difference':mp.mpf(0)}for f in FIELDS};allpassed=True;total=0
 for c in source['cases']:
  name=c['case'];controller,rc,wc,jc=name.split('__')
  k='5/48'if controller=='original'else'29/48';w={'w0':'0','wplus':'1/100','wminus':'-1/100'}[wc]
  H=F(1,2)if jc=='plus_to_half'else F(1)
  cuts=sorted(set([F(0),H]+([F(1,8),F(3,8)]if rc=='r80_120_80'else[])+([F(1,4),F(1,2)]if jc=='plus_minus_zero'else[])))
  with (HERE/c['trace']).open()as f:rows=list(csv.DictReader(f))
  y=mp.matrix([0,0,0,0,1]);q=mp.matrix([0,0,0]);idx=0;maxerr={f:mp.mpf(0)for f in FIELDS};peaks={f:{'value':mp.mpf(0),'time_s':mp.mpf(0),'side':'regular'}for f in METRICS};boundary=[]
  for si,(t0,t1)in enumerate(zip(cuts,cuts[1:])):
   r=(120 if F(1,8)<=t0<F(3,8)else 80)if rc=='r80_120_80'else int(rc[1:])
   j=10 if jc=='plus_to_half'or t0<F(1,4)else(-10 if t0<F(1,2)else 0)
   transition=step(r,w,j,k);n=int((t1-t0)*2000);qstart=q.copy()
   for m in range(n+1):
    if m:y=transition*y
    tau=mp.mpf(m)/2000
    qt=mp.matrix([qstart[0]+qstart[1]*tau+qstart[2]*tau**2/2+j*tau**3/6,qstart[1]+qstart[2]*tau+j*tau**2/2,qstart[2]+j*tau])
    out=output(y,qt,j,k,r,w);row=rows[idx];idx+=1;tm=M(t0)+tau
    assert abs(mp.mpf(row['t_s'])-tm)<mp.mpf('1e-15')
    assert int(row['segment'])==si and int(row['r_per_s'])==r and int(row['reference_jerk_m_per_s3'])==j
    for field in FIELDS:
     delta=abs(mp.mpf(row[field])-out[field]);maxerr[field]=max(maxerr[field],delta)
     if delta>globalworst[field]['max_abs_difference']:globalworst[field]={'max_abs_difference':delta,'case':name,'time_s':str(tm),'side':row['event_side']}
    for field in METRICS:
     if abs(out[field])>abs(peaks[field]['value']):peaks[field]={'value':out[field],'time_s':tm,'side':row['event_side']}
    if m in [0,n]:boundary.append({'segment':si,'time_s':str(tm),'side':'start'if m==0 else'end','xi':[mp.nstr(y[i],65)for i in range(4)],'q_physical':[mp.nstr(v,65)for v in qt]})
   q=qt
  assert idx==len(rows);total+=idx
  passed=all(d<=TOL for d in maxerr.values());within=abs(peaks['ex_m']['value'])<=R
  assert within==c['within_position_target_at_samples']
  allpassed&=passed
  cases.append({'case':name,'samples_checked':idx,'passed_absolute_tolerance':passed,'max_abs_difference':{f:mp.nstr(d,25)for f,d in maxerr.items()},'within_position_target_at_samples':bool(within),'high_precision_sampled_peaks':{f:{'signed_value':mp.nstr(v['value'],65),'max_abs':mp.nstr(abs(v['value']),65),'time_s':str(v['time_s']),'side':v['side']}for f,v in peaks.items()},'segment_boundary_states':boundary})
 report={'passed':bool(allpassed),'method':'80-decimal-digit mpmath Taylor exponential of independently assembled augmented 5x5 forced system, then uniform-step recurrence. Independent schedule/reference construction; no reuse of SciPy segment-start states. Every trace sample checked.','precision_decimal_digits':80,'mpmath_version':mp.__version__,'python':sys.version,'absolute_comparison_tolerance':'2e-10 in each column unit','samples_checked':total,'case_count':len(cases),'global_max_abs_difference':{f:{k:mp.nstr(v,25)if isinstance(v,mp.mpf)else v for k,v in data.items()}for f,data in globalworst.items()},'seconds':time.monotonic()-started,'cases':cases}
 (HERE/'high-precision-check.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:report[k]for k in ['passed','case_count','samples_checked','seconds','global_max_abs_difference']},indent=2));assert allpassed
if __name__=='__main__':main()
