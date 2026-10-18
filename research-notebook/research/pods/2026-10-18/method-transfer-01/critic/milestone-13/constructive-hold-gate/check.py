"""Exact clock and guard arithmetic for a statement gate; no ODE simulation."""
from fractions import Fraction as F
from pathlib import Path
import json
h=F(1,2000)
rows=[]
for n in range(1,5):
 t=n*h
 incoming=max(0,n-2);outgoing=n-1
 stamp_in=incoming*h;stamp_out=outgoing*h
 assert t-stamp_in<=2*h and t-stamp_out==h
 rows.append({'boundary':str(t),'incoming_command':'pending' if n==1 else f'clip(command(m_{incoming}))','outgoing_command':f'clip(command(m_{outgoing}))','incoming_stamp':str(stamp_in),'outgoing_stamp':str(stamp_out),'incoming_age':str(t-stamp_in),'outgoing_age':str(t-stamp_out)})
true_speed_guard=F(561,50000)+F(1,100)
sigma_lower=(F(39,100)-true_speed_guard)/F(61,50)
assert true_speed_guard==F(1061,50000)
assert sigma_lower==F(18439,61000) and sigma_lower>F(1,20)
assert F(604,2000)<sigma_lower<=F(605,2000)
last_sample=1058*h;last_dispatch=last_sample+h;horizon=F(53,100)
assert last_sample==F(529,1000) and last_dispatch==F(1059,2000)
assert horizon-last_dispatch==h
assert F(1,1000)+h>F(1,1000)
# A current-state sample exists at cell start, but its specified arrival is one
# cell later. This falsifies the fixed-delay schedule, not mathematical causality.
assert 2*h+h>2*h
result={'scope':'Exact clock and threshold controls only. The flow formula is checked analytically in REPORT.txt; no recurrence or Lean theorem implemented.',
 'boundary_rows':rows,'true_speed_guard':str(true_speed_guard),'first_hit_time_lower':str(sigma_lower),'first_hit_index_lower_if_on_grid':605,
 'candidate_C6_index_upper':1058,'latest_sample':str(last_sample),'latest_dispatch':str(last_dispatch),'strict_terminal_reserve':str(horizon-last_dispatch),
 'wrong_period_plus_latency':str(F(1,1000)+h),'age_limit':str(2*h),'all_checks_pass':True}
Path(__file__).with_name('result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
