"""Exact budget arithmetic plus reuse of the old binary64 reachability diagnostic.
The Lean theorems remain the proof. No new trajectory integration is performed.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json
HERE=Path(__file__).resolve().parent
WORK=HERE.parents[5]
source=WORK/'research/pods/2026-10-18/recovery-handoff-02/root-admission-reachability-screen.json'
def rat(x):return {'rational':str(x),'decimal':float(x)}
R=F(2221,40000);D=F(1,2000);V=F(613,20000);A=F(13,10);J=F(756,25)
e0=F(1,1000)+V*D;e1=F(1,100)+A*D;e2=F(1,20)+J*D
budgets=[e0+F(1,50)/4+F(5,4)/32,e0+e1/4+F(5,4)/32,
         e0+e1/2+e2/16+F(1,50)/4+F(5,4)/32]
assert max(budgets)<R
rows=[]
for row in json.loads(source.read_text())['rows']:
 x,v,a=row['first_zero_state'];c=x+v/4+a/32
 rows.append({'rate':row['r'],'first_zero_state_binary64':row['first_zero_state'],
  'old_fixed_position_box_unreachable_in_diagnostic':row['peak_below_fixed_admission_minimum_0_139'],
  'nominal_guard_passes_binary64':abs(v)<=.02 and abs(a)<=1.25,
  'all_sensor_errors_pass_via_subband_binary64':abs(v)<=.01 and abs(a)<=1.20,
  'nominal_adaptive_center_binary64':c,'nominal_tube_binary64':[c-float(R),c+float(R)],
  'tube_upper_below_015_binary64':c+float(R)<=.15})
report={'scope':'Exact rational startup arithmetic; old trajectory values are binary64 diagnostics, not a Lean or interval reachability proof. No sampled detector or continuation existence is constructed by this screen.',
 'source':str(source.relative_to(WORK)),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
 'startup_budgets':[rat(x) for x in budgets],'smallest_margin':rat(R-max(budgets)),
 'mixed_history_residual':rat(F(111,1000)),'residual_margin':rat(2*R-F(111,1000)),
 'diagnostic_rows':rows,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(HERE/'admission-screen.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'exact_budgets_pass':True,'diagnostic_rows':len(rows)}))
