#!/usr/bin/env python3
"""Independent exact rational Bernstein enclosure of the frozen reference jerk.
This is a Python exact-arithmetic cross-check, not a new kernel theorem.
"""
from pathlib import Path
from fractions import Fraction as Q
from math import comb
import hashlib,json
HERE=Path(__file__).resolve().parent
SOURCE=HERE.parent.parent/'causal-stop-05/builder/reference.json'
def derivative(cs):return [i*c for i,c in enumerate(cs)][1:] or [Q(0)]
def enclosure(cs,lo,hi):
    n=len(cs)-1
    # Coefficients of p(lo+(hi-lo)*u).
    power=[sum(cs[i]*comb(i,k)*lo**(i-k)*(hi-lo)**k for i in range(k,n+1)) for k in range(n+1)]
    b=[sum(power[i]*Q(comb(k,i),comb(n,i)) for i in range(k+1)) for k in range(n+1)]
    return b
rows=[]
for phase in json.loads(SOURCE.read_text()):
    cs=list(map(Q,phase['position_coefficients_local_time']))
    for _ in range(3):cs=derivative(cs)
    while len(cs)>1 and cs[-1]==0:cs.pop()
    duration=Q(phase['end'])-Q(phase['start']);pending=[(Q(0),duration,0)];cells=[]
    while pending:
        lo,hi,depth=pending.pop();bs=enclosure(cs,lo,hi)
        if max(map(abs,bs))<=10:
            cells.append({'lo':str(lo),'hi':str(hi),'bernstein_coefficients':list(map(str,bs))})
        else:
            assert depth<8,(phase['name'],lo,hi,bs)
            mid=(lo+hi)/2;pending.extend([(mid,hi,depth+1),(lo,mid,depth+1)])
    cells.sort(key=lambda r:Q(r['lo']))
    assert Q(cells[0]['lo'])==0 and Q(cells[-1]['hi'])==duration
    assert all(Q(a['hi'])==Q(b['lo']) for a,b in zip(cells,cells[1:]))
    rows.append({'name':phase['name'],'third_derivative_coefficients':list(map(str,cs)),'closed_cells':cells})
result={'passed':True,'method':'Exact rational Bernstein convex-hull enclosures; all closed cells cover every phase and every coefficient lies in [-10,10]. Python cross-check, not a kernel theorem.',
        'reference_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'phases':rows}
(HERE/'exact_reference_audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed':True,'phases':len(rows),'closed_cells':sum(len(p['closed_cells']) for p in rows)}))
