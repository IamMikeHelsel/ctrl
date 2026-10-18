"""Independent arithmetic evidence. Does not import the Lean fixture generator or lead code."""
from pathlib import Path
from fractions import Fraction as Q
from random import Random
import json,hashlib
HERE=Path(__file__).resolve().parent
LEAD=HERE.parent.parent/'lead-01'

def K(z):
 if z<=0:return Q(0)
 if z<=1:return z
 if z<=2:return 4-3*z
 if z<=3:return 3*z-8
 if z<=4:return 4-z
 return Q(0)
def jerk(es,h,t):return sum((d*K((t-a)/h)/h**3 for a,d in es),Q(0))
def hinge(es,h,t):return sum((d/h**4*sum((Q(k)*max(t-(a+i*h),Q(0)) for i,k in enumerate([1,-4,6,-4,1])),Q(0)) for a,d in es),Q(0))
def knots(es,h,c):return sorted({c}|{a+i*h for a,_ in es for i in range(5) if a+i*h>=c})
def guard(es,h,J,c):return max(abs(jerk(es,h,t)) for t in knots(es,h,c))<=J

def main():
 spec=json.loads((LEAD/'fixed-streams.json').read_text())
 expected={c['case']:c for c in json.loads((LEAD/'reference-checks.json').read_text())['cases']}
 h=Q(spec['h_s']);J=Q(spec['reference_jerk_limit_m_s3']);tick=Q(spec['commit_tick_s'])
 rows=[]; admission_count=0
 for c in spec['cases']:
  batches={}
  for p in c['packets']:
   ready=Q(p['ready_s']);u=ready/tick;commit=Q(-(-u.numerator//u.denominator))*tick
   batches.setdefault(commit,[]).append(p)
  es=[];target=Q(0);mark=-1;out=[]
  for now,ps in sorted(batches.items()):
   p=max(ps,key=lambda p:p['sequence'])
   if p['sequence']<=mark:continue
   mark=p['sequence'];delta=Q(p['target_m'])-target
   candidate=es+([(now,delta)] if delta else [])
   ok=guard(candidate,h,J,now); admission_count+=1
   out.append((p['sequence'],ok))
   if ok:es=candidate;target=Q(p['target_m'])
  old=expected[c['id']]
  want=[(Q(x['time_s']),Q(x['delta_m'])) for x in old['accepted_events']]
  assert es==want and target==Q(old['final_accepted_goal_m'])
  assert out==[(o['sequence'],o['outcome']=='accepted') for o in old['outcomes'] if o['outcome'] in ('accepted','jerk_rejected')]
  peak=max(abs(jerk(es,h,t)) for t in knots(es,h,Q(0)))
  assert peak==Q(old['exact_reference_jerk_peak_m_s3'])
  assert all(jerk(es,h,t)==hinge(es,h,t) for t in knots(es,h,Q(0)))
  rows.append({'case':c['id'],'events':len(es),'peak':str(peak),'admissions':len(out),'passed':True})
 rng=Random(20261018); interiors=0
 for _ in range(256):
  h=Q(rng.randint(1,6),5);c=Q(rng.randint(-10,30),5)
  es=[(Q(rng.randint(-10,30),5),Q(rng.randint(-8,8),11)) for _ in range(rng.randint(0,9))]
  points=knots(es,h,c)
  for a,b in zip(points,points[1:]):
   for ratio in [Q(1,5),Q(1,2),Q(4,5)]:
    t=a+ratio*(b-a)
    assert jerk(es,h,t)==(1-ratio)*jerk(es,h,a)+ratio*jerk(es,h,b)
    assert jerk(es,h,t)==hinge(es,h,t)
    interiors+=1
  t=max(points)+10*h
  assert jerk(es,h,t)==0
 tests={'omit_current':guard([(Q(0),Q(1))],Q(1),Q(1,4),Q(7,2)) is False,
 'omit_interior':jerk([(Q(0),Q(1))],Q(1),Q(0))==0 and jerk([(Q(0),Q(1))],Q(1),Q(4))==0 and jerk([(Q(0),Q(1))],Q(1),Q(2))==-2,
 'erase_future':guard([(Q(0),Q(1)),(Q(1,4),Q(-1))],Q(1),Q(1),Q(0)) and not guard([(Q(0),Q(1))],Q(1),Q(1),Q(0))}
 assert all(tests.values())
 result={'passed':True,'authority':'Independent finite arithmetic only; Lean check is the certificate authority.','cases':rows,'admission_count':admission_count,'additional_histories':256,'interior_affine_checks':interiors,'negative_witnesses':tests,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
 (HERE/'independent-arithmetic.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
