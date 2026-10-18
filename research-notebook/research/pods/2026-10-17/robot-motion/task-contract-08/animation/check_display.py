"""Exact rational display anchors and frozen source bindings; not a new proof."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib,json,datetime

HERE=Path(__file__).resolve().parent
def response(z):
    return sum(c*max(z-k,Q(0))**4 for k,c in enumerate([1,-4,6,-4,1]))/24
def q(t):return Q(1,50)*response((t-Q(11,50))/Q(1,5))
assert q(Q(11,50))==0
assert q(Q(31,50))==Q(1,100)
assert q(Q(51,50))==Q(1,50)
assert q(Q(2))==Q(1,50)
assert Q(1,100)-Q(1,5000)==Q(49,5000)
assert Q(1,50)-(Q(1,100)+Q(1,5000))==Q(49,5000)
assert Q(51,50)<=Q(3,2)<=2
files=[HERE.parent/'builder'/n for n in ['TaskFixtures.lean','TaskContract.lean','TaskShape.lean','IsolatedHistory.lean','source-freeze.json','freeze-status.json']]
files += [HERE.parent/'grader'/n for n in ['proof-review.json','contract-review.txt']]
out={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'scope':'Exact rational plotted anchors and source bindings. Conditional theorem interpretation independently accepted by controls_direct_independent_review. No physical trace is generated.',
    'reference_position_mm':{'0.22':str(q(Q(11,50))*1000),'0.62':str(q(Q(31,50))*1000),'1.02':str(q(Q(51,50))*1000),'2':str(q(Q(2))*1000)},
    'position_tube_radius_m':'1/5000','midpoint_lower_position_m':'49/5000','wrong_midpoint_deadline_min_error_m':'49/5000',
    'source_bindings':{str(p.relative_to(HERE.parent.parent)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},'passed':True}
(HERE/'display-check.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
