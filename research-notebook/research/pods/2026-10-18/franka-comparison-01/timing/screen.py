from fractions import Fraction as F
from pathlib import Path
import json,hashlib
P=Path(__file__).resolve().parent
oldR=F(2221,40000);R=F(567,10000);D=F(1,2000);W=F(283,2500);g=F(3,5000)
Kmax=F(2407079,50250000);noise=F(103,1000)
def obj(x):return {'exact':str(x),'decimal':float(x)}
def slope(a,k):return 96*k+6*(noise+a*(384*k+F(618,1000)))
def first(a,d,k):return noise+8*d+slope(a,k)*(a-d)
def closed(a,d,k):return noise+8*d+108*k*(a-d)
def minimum(a,d):return (noise+8*d+F(618,1000)*(a-d)*(1+6*a))/(2-(a-d)*(96+2304*a))
def maximum(a,d,w):return (w-noise-8*d)/(108*(a-d))
rows=[]
for a in [F(1,1000),F(5,4000),F(3,2000),F(8,5000)]:
 rows.append({'age':obj(a),'delay_cap':obj(D),'old_support_W1':obj(first(a,D,oldR)),'old_support_pass':first(a,D,oldR)<=2*oldR,'new_support_W1':obj(first(a,D,R)),'new_support_pass':first(a,D,R)<=2*R,'new_closed_W':obj(closed(a,D,R)),'rounded_W_pass':closed(a,D,R)<=W,'same_drift_radius_interval':[obj(minimum(a,D)),obj(maximum(a,D,W))]})
a=F(3,2000)
result={'scope':'Exact rational certificate screen; not numerical simulation, a trajectory counterexample, or hardware measurement.',
'rows':rows,'T1':{'period':obj(F(1,1000)),'illustrative_delay':obj(D),'max_age':obj(a),'old_R':obj(oldR),'new_R':obj(R),'W1_old':obj(first(a,D,oldR)),'old_failure_gap':obj(first(a,D,oldR)-2*oldR),'W1_new':obj(first(a,D,R)),'new_prefix_margin':obj(2*R-first(a,D,R)),'S_at_Kmax_for_barrier':obj(slope(a,F(1,16))),'new_closed_W':obj(closed(a,D,R)),'rounded_W':obj(W),'new_drift':obj(g),'old_drift':obj(F(3,1700)),'new_max_entry_duration':obj((Kmax-F(9,200))/g),'old_max_entry_duration':obj((Kmax-F(9,200))/F(3,1700)),'initial_weighted_radius_max_unchanged':obj(Kmax),'forward_ceiling_unchanged':obj(F(3013722449,20100000000)),'clearance_margin_unchanged':obj(F(1277551,20100000000)),'command_clipping_bound_at_support':obj(24*R+F(93,1000)),'derived_effective_target_bound':obj(24*R+noise),'clipping_bound_all_inflation_K':obj(24*F(1,16)+F(93,1000)),'velocity_support_bound':obj(8*R),'acceleration_support_bound':obj(64*R),'naive_face':obj(-F(19,10)*F(9,200)+F(3,4)*F(115,1000)),'rounded_face':obj(-F(19,10)*F(9,200)+F(3,4)*W)}}
assert first(a,D,oldR)>2*oldR and first(a,D,R)<2*R
assert closed(a,D,R)<W and slope(a,F(1,16))<8
assert -F(19,10)*F(9,200)+F(3,4)*W==-g
result['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
(P/'screen-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result['T1'],indent=2))
