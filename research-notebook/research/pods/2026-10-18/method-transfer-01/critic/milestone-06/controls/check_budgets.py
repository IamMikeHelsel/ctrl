#!/usr/bin/env python3
from pathlib import Path
from fractions import Fraction as F
from itertools import product
import hashlib,json
p=Path(__file__).parent;R=F(2221,40000);D=F(1,2000)
V=F(613,20000);A=F(13,10);J=F(756,25)
e0=F(1,1000)+V*D;e1=F(1,100)+A*D;e2=F(1,20)+J*D
budgets=[e0+F(1,50)/4+F(5,4)/32,e0+e1/4+F(5,4)/32,e0+e1/2+e2/16+F(1,50)/4+F(5,4)/32]
assert budgets==[F(1803113,40000000),F(1709613,40000000),F(2178913,40000000)]
assert R-max(budgets)==F(42087,40000000)>0
# Multi-affine feedback derivative: exact box extrema occur at these corners.
slopes=[-8*v-6*a-r*(-F(121,100)+d-a)/2 for v,a,r,d in product([-V,V],[-A,A],[F(8),F(12)],[-F(1,100),F(1,100)])]
assert min(slopes)==F(4887,2500)>0 and max(slopes)==F(19313,2500)<8
K=F(1,16);W0=F(103,1000)+(384*K+F(618,1000))/1000
assert 96*K+6*W0<8
W=F(103,1000)+F(8,1000);assert 2*R-W==F(1,20000)>0
assert 24*K+F(93,1000)<2
m=[F(7,50),-F(1,100),-F(117,100)];c=m[0]+m[1]/4+m[2]/32
u=-8*(m[0]-c)-6*m[1]-m[2]/2
assert c==F(323,3200) and u==F(133,400)
assert m[0]-c==F(5,128) and c+R==F(12517,80000)>F(3,20)
assert 24*R+F(103,1000)==F(3589,2500)
# Explicit independent sensor-box initial failures for two widened guards.
cases=[]
for v,a,sv,sa in [(F(3,100),F(5,4),F(4,100),F(13,10)),(F(1,50),F(7,5),F(3,100),F(29,20))]:
 cc=v/4+a/32;z=F(1,1000)-cc+sv/2+sa/16
 assert abs(sv-v)<=F(1,100) and abs(sa-a)<=F(1,20) and z>R
 cases.append({'measured_v':str(v),'measured_a':str(a),'coordinate_2':str(z),'excess_over_R':str(z-R)})
# Recompute the existing three numerical rows without integrating a new path.
screen=json.loads((p/'inputs/admission-screen.json').read_text());work=next(q for q in p.resolve().parents if (q/'lean-controls/lean-toolchain').is_file());old=work/screen['source']
assert hashlib.sha256(old.read_bytes()).hexdigest()==screen['source_sha256']
source_rows=json.loads(old.read_text())['rows'];rows=[]
for source,row in zip(source_rows,screen['diagnostic_rows']):
 x,v,a=source['first_zero_state'];center=x+v/4+a/32
 assert row['nominal_adaptive_center_binary64']==center
 assert row['nominal_tube_binary64']==[center-float(R),center+float(R)]
 assert row['nominal_guard_passes_binary64']==(abs(v)<=.02 and abs(a)<=1.25)
 assert row['all_sensor_errors_pass_via_subband_binary64']==(abs(v)<=.01 and abs(a)<=1.20)
 rows.append({'rate':source['r'],'tube_upper_binary64':center+float(R),'below_015':center+float(R)<=.15})
assert len(rows)==len(source_rows)==len(screen['diagnostic_rows'])==3
out={'passed':True,'exact_startup_budgets':list(map(str,budgets)),'minimum_margin':str(R-max(budgets)),'exact_pending_slope_extrema':list(map(str,[min(slopes),max(slopes)])),'mixed_history_residual':str(W),'residual_margin':str(2*R-W),'nominal_center':str(c),'nominal_command':str(u),'nominal_tube':list(map(str,[c-R,c+R])),'nominal_reference_behind_measured_position':str(m[0]-c),'widened_initial_guard_negatives':cases,'existing_binary64_diagnostic_rows':rows,'scope':'Exact scalar budgets plus arithmetic reuse of existing binary64 states; no new trajectory or detector proof.'}
(p/'budget-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
