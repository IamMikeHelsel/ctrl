from pathlib import Path
from fractions import Fraction as F
from math import comb, factorial
from collections import defaultdict
import hashlib,json
ROOT=Path(__file__).resolve().parents[4]
HERE=Path(__file__).resolve().parent
B=ROOT/'research/overnight/2026-10-18/robot-motion/builder-03'
rows=json.loads((B/'metrics.json').read_text())['rows']
fine=[r for r in rows if r['sample_step_s']==.0005]
assert len(rows)==72 and len(fine)==36
methods=['fir_checked','native_fast','native_matched']
keys=[('jerk','suffix_until_horizon_jerk_energy_m2_s5',1),('excursion','suffix_until_horizon_extra_forward_excursion_m',1000),('path','suffix_until_horizon_path_length_m',1000),('command_TV','suffix_until_horizon_command_total_TV_m_s2',1)]
expected=[['6.067--6.121','17.307--17.494','15.171--15.250'],['14.315--14.331','6.851--6.872','6.851--6.872'],['32.650--32.669','17.734--17.763','17.723--17.770'],['1.973--1.978','2.771--2.881','2.610--2.780']]
report={'rounded_ranges':{},'task_counts':{},'ratios':{}}
for (label,key,scale),exp in zip(keys,expected):
 actual=[]
 for m in methods:
  vals=[scale*r[key] for r in fine if r['method']==m and r['case']=='return_generous']
  assert len(vals)==6
  actual.append(f'{min(vals):.3f}--{max(vals):.3f}')
 assert actual==exp,(label,actual,exp)
 report['rounded_ranges'][label]=actual
for case,exp in [('return_generous',[6,6,6]),('return_tight',[0,6,0])]:
 counts=[sum(r['full_task_pass'] for r in fine if r['case']==case and r['method']==m) for m in methods]
 assert counts==exp;report['task_counts'][case]=counts
for label,key,_ in keys[:2]:
 pairs=[]
 for rate in [80,100,120]:
  for d in [0,.01]:
   def get(m):return next(r for r in fine if r['case']=='return_generous' and r['method']==m and r['rate']==rate and r['disturbance']==d)[key]
   pairs.append(get('fir_checked')/get('native_matched'))
 report['ratios'][label]=[min(pairs),max(pairs)]
assert [f'{v:.3f}' for v in report['ratios']['jerk']]==['0.398','0.402']
assert [f'{v:.3f}' for v in report['ratios']['excursion']]==['2.085','2.090']
def derivative(t,order,events):
 h=F(1,5)
 return sum(delta*sum((-1)**k*comb(4,k)*max((t-tau)/h-k,F(0))**(4-order) for k in range(5))/(factorial(4-order)*h**order) for tau,delta in events)
events=[(F(11,50),F(1,50)),(F(31,50),F(-1,50))]
reference=[derivative(F(13,25),i,events) for i in range(4)]
assert reference==[F(77,19200),F(23,480),F(5,16),F(-5,4)]
progress=derivative(F(1,2),0,events)
assert progress==F(779,250000)
assert progress-2*F(1,5000)>=F(1,1000)
assert F(1,100)+F(15,2)/(48*10)==F(41,1600)<=2*10**2*F(1,5000)
report['independent_fraction_fixture']={'revision_jet':[str(x) for x in reference],'progress_reference_m':str(progress),'progress_physical_lower_m':str(progress-2*F(1,5000)),'budget_left':str(F(41,1600)),'budget_right':str(2*10**2*F(1,5000))}
report['inputs']={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [B/'metrics.json',B/'artifact-sha256.json']}
report['scope']='Independent aggregation and exact polynomial fixture arithmetic, not a new physical trace replay.'
report['passed']=True
(HERE/'paper-numbers.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
