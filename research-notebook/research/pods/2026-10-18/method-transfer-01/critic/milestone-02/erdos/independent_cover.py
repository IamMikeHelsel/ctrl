"""Independent E1 verifier: vertical-strip coverage and expanded rational bounds.

Does not import either builder verifier or interval generator. No floating-point
value decides a check. This is arithmetic evidence, not a kernel proof.
"""
from pathlib import Path
from fractions import Fraction as Q
import json,copy

P=Path(__file__).resolve().parent
R=Q(1293,50000);I=Q(2,47);A=Q(1559,2000);H=Q(781,1000);J0=Q(423,10000)
YL,YH=Q(500,781),Q(1000,1559)
K=4*(4*R+1)

def geometry(leaves):
    boxes=[]
    for leaf in leaves:
        yl,yh=map(Q,leaf['y']);jl,jh=map(Q,leaf['j'])
        assert YL<=yl<yh<=YH and J0<=jl<jh<=I
        boxes.append((yl,yh,jl,jh))
    cuts=sorted({q for box in boxes for q in box[:2]}|{YL,YH})
    for left,right in zip(cuts,cuts[1:]):
        mid=(left+right)/2
        intervals=sorted((jl,jh) for yl,yh,jl,jh in boxes if yl<mid<yh)
        cursor=J0
        for lo,hi in intervals:
            assert lo==cursor,'hole or interior overlap in a vertical strip'
            cursor=hi
        assert cursor==I,'incomplete vertical strip'
    area=sum((yh-yl)*(jh-jl) for yl,yh,jl,jh in boxes)
    assert area==(YH-YL)*(I-J0)
    return len(cuts)-1,area

def check(data):
    assert Q(data['R'])==R and Q(data['I'])==I
    assert tuple(map(Q,data['rectangle']['y']))==(YL,YH)
    assert tuple(map(Q,data['rectangle']['j']))==(J0,I)
    leaves=[]
    for n in data['cover']:
        assert type(n['accepted']) is bool
        if n['accepted']:leaves.append(n)
    assert len(leaves)==272
    strips,area=geometry(leaves)
    # Algebraically equivalent expressions with cancellation performed first:
    # C=(1+16R)j-4Ry^2-K j^2/y^2;
    # L=8Ry-Kj/y; B=(j-R)/(y-1/2)-L;
    # S=B^2/4-j+4Ry^2-Kj^2/y^2.
    # All factors used in the monotone endpoint bounds below are positive.
    bounds=[]
    for number,n in enumerate(leaves):
        yl,yh=map(Q,n['y']);jl,jh=map(Q,n['j'])
        assert yl>Q(1,2) and jl>R>0
        C_up=(1+16*R)*jh-4*R*yl*yl-K*jl*jl/(yh*yh)
        L_lo=8*R*yl-K*jh/yl
        L_hi=8*R*yh-K*jl/yh
        B_lo=(jl-R)/(yh-Q(1,2))-L_hi
        B_hi=(jh-R)/(yl-Q(1,2))-L_lo
        assert 0<B_lo<=B_hi
        S_up=B_hi*B_hi/4-jl+4*R*yh*yh-K*jl*jl/(yh*yh)
        assert C_up<0 and S_up<0,'expanded expression did not certify a leaf'
        bounds.append({'leaf':number,'C_upper':str(C_up),'S_upper':str(S_up),'B_lower':str(B_lo)})
    return {'vertical_strips':strips,'exact_area':str(area),'leaves':len(leaves),
            'max_C_upper':str(max(Q(v['C_upper']) for v in bounds)),
            'max_S_upper':str(max(Q(v['S_upper']) for v in bounds)),
            'expanded_bounds':bounds}

data=json.loads((P/'inputs/certificate.json').read_text())
result=check(data)
assert Q(1,2)<A<Q(7797,10000)<H<Q(4,5)<1
assert (YL,YH)==(1/(2*H),1/(2*A)) and YL>Q(1,2)
assert I>J0>0
low_cap=R-I*A*A;low_j=R-H*H*J0
assert low_cap>0 and low_j>0
poly=(R-Q(3,8),Q(7,8),R-I-Q(17,32))
value=lambda c:poly[0]+poly[1]*c+poly[2]*c*c
end=Q(4,5)
slope=(value(end)-value(H))/(end-H)
chord=(value(H)-slope*H,slope,Q(0))
assert tuple(p-c for p,c in zip(poly,chord))==(poly[2]*H*end,-poly[2]*(H+end),poly[2])
assert poly[2]<0 and value(H)>0 and value(end)>0
aa=R+Q(1,4)-I;bb=Q(3,8);cc=R+Q(1,8);disc=4*aa*cc-bb*bb
assert aa>0 and disc>0
assert (4*aa*cc,-4*aa*bb,4*aa*aa)==(bb*bb+disc,-4*aa*bb,4*aa*aa)

# Check exact expanded identities independently on the whole polynomial algebra
# after multiplying C by y^2 and S by 4*y^2*(y-1/2)^2. Coefficients are obtained
# with a minimal two-variable polynomial engine, not an external CAS.
def add(a,b):
    out=a.copy()
    for k,v in b.items():out[k]=out.get(k,Q(0))+v
    return {k:v for k,v in out.items() if v}
def scale(a,c):return {k:v*c for k,v in a.items() if v*c}
def mul(a,b):
    out={}
    for (i,j),u in a.items():
        for (k,l),v in b.items():out[(i+k,j+l)]=out.get((i+k,j+l),Q(0))+u*v
    return {k:v for k,v in out.items() if v}
def sq(a):return mul(a,a)
y={(1,0):Q(1)};j={(0,1):Q(1)};one={(0,0):Q(1)}
b=add(y,scale(one,Q(-1,2)))
mu_num=scale(j,2)
diff_num=add(sq(y),scale(mu_num,-1))
L_num=add(scale(diff_num,8*R),scale(mu_num,-2))
C_num=add(add(mul(j,sq(y)),scale(sq(diff_num),-4*R)),scale(sq(mu_num),-1))
C_exp=add(add(scale(mul(j,sq(y)),1+16*R),scale(sq(sq(y)),-4*R)),scale(sq(j),-K))
assert C_num==C_exp
B_num=add(mul(add(j,scale(one,-R)),y),scale(mul(L_num,b),-1))
S_num=add(sq(B_num),scale(mul(add(mul(L_num,mu_num),scale(C_num,-1)),sq(b)),4))
S_exp=add(sq(B_num),scale(mul(add(add(scale(mul(j,sq(y)),-1),scale(sq(sq(y)),4*R)),scale(sq(j),-K)),sq(b)),4))
assert S_num==S_exp

negatives=[]
leaves=[n for n in data['cover'] if n['accepted']]
try:geometry(leaves[1:])
except AssertionError:negatives.append('missing geometric leaf rejected')
else:raise AssertionError('missing leaf accepted')
bad=copy.deepcopy(data);bad['R']='1/50'
try:check(bad)
except AssertionError:negatives.append('changed target rejected')
else:raise AssertionError('changed target accepted')

result.update({'scope':'Independent whole-rectangle bound and five-region arithmetic, no new Lean theorem.',
 'all_checks_pass':True,'expanded_polynomial_identities':True,
 'outer_regions':{'cap_margin':str(low_cap),'low_j_margin':str(low_j),
                 'middle_left':str(value(H)),'middle_right':str(value(end)),
                 'upper_discriminant':str(disc),'full_c_j_coverage':True},
 'negative_controls':negatives})
(P/'independent-cover-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='expanded_bounds'},indent=2))
