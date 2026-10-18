"""Exact local algebra controls; not a universal parameter certificate."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib,json

def values(R,y,j):
    mu=2*j/y; L=8*R*(y-mu)-2*mu
    C=j-4*R*(y-mu)**2-mu**2
    B=(j-R)/(y-Q(1,2))-L
    S=B*B/4+L*mu-C
    # Coefficients ordered constant, linear, quadratic.
    low=[j-4*R*y*y,8*R*y,-4*R-1]
    low_expanded=[C-L*mu-(4*R+1)*mu*mu,L+2*(4*R+1)*mu,-4*R-1]
    high=[Q(0),(j-R)/(y-Q(1,2)),Q(-1)]
    high_expanded=[C+S-L*mu-B*B/4,L+B,Q(-1)]
    assert low==low_expanded and high==high_expanded
    return {'C':C,'S':S,'C_plus_S':C+S,'R':R,'y':y,'j':j}

rows={
 'old_failed_tangent':values(Q(1293,50000),Q(50,79),Q(2,47)),
 'new_grid_obstruction':values(Q(16,625),1/(2*Q(1259,1600)),Q(2,47)*Q(236,240)),
 'must_reject':values(Q(1,50),Q(2,3),Q(2,47))
}
assert rows['old_failed_tangent']['S']>0
assert rows['old_failed_tangent']['C']<0 and rows['old_failed_tangent']['C_plus_S']<0
assert rows['new_grid_obstruction']['S']>0
assert rows['new_grid_obstruction']['C']<0 and rows['new_grid_obstruction']['C_plus_S']<0
assert rows['must_reject']['C']>0 or rows['must_reject']['C_plus_S']>0
out={'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'scope':'Exact coefficient identities at three rational points and negative controls; no domain cover.',
     'checks':{k:{n:str(v) for n,v in row.items()} for k,row in rows.items()}}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
