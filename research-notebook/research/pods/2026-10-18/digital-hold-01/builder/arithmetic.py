#!/usr/bin/env python3
"""Exact explanatory arithmetic. Lean proves the symbolic prefix bound."""
from fractions import Fraction as F
from pathlib import Path
import json
R=F(2221,40000);M=F(93,1000);D=F(1,100)
rows=[]
for radius,age in [(R,F(1,1000)),(R,F(1,200)),(F(1,20),F(1,1000))]:
    raw=48*radius+M+D
    L0=96*radius+6*raw
    W0=M+D+age*L0
    L1=96*radius+6*W0
    W1=M+D+age*L1
    row={'radius':radius,'age':age,'raw_mismatch':raw,'coarse_slope':L0,
         'first_age_mismatch':W0,'refined_slope':L1,'second_age_mismatch':W1,
         'cube_budget':2*radius,'slack':2*radius-W1}
    rows.append({k:{'exact':str(v),'decimal':float(v)} for k,v in row.items()})
assert F(rows[0]['second_age_mismatch']['exact'])==F(136350047,1250000000)
assert F(rows[0]['slack']['exact'])>0
assert F(rows[1]['slack']['exact'])<0
assert F(rows[2]['slack']['exact'])<0
out={'status':'exact fraction arithmetic; safety and prefix bound are separately proved in Lean',
     'rows':rows,'interpretation':'Rejected sufficient bounds are not unsafe plant trajectories.'}
Path(__file__).with_name('arithmetic-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
