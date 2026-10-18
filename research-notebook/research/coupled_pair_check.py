"""Independent exact-rational check of one coupled-pair calibration problem.

This checks a fixed known family, not the universal order-six conjecture.
No floating-point arithmetic or external packages are used.
"""
from fractions import Fraction as F
from pathlib import Path
import json

N = 6
def zero(): return [[F(0) for _ in range(N)] for _ in range(N)]
def transpose(a): return [list(row) for row in zip(*a)]
def add(a,b): return [[a[i][j]+b[i][j] for j in range(N)] for i in range(N)]
def sub(a,b): return [[a[i][j]-b[i][j] for j in range(N)] for i in range(N)]
def mul(a,b): return [[sum(a[i][k]*b[k][j] for k in range(N)) for j in range(N)] for i in range(N)]
def square_sum(a): return sum(v*v for row in a for v in row)
def upper(a): return [a[i][j] for i in range(N) for j in range(i+1,N)]
def rank(a):
    a=[list(map(F,row)) for row in a]
    pivot=0
    for j in range(len(a[0])):
        k=next((i for i in range(pivot,len(a)) if a[i][j]),None)
        if k is None: continue
        a[pivot],a[k]=a[k],a[pivot]
        scale=a[pivot][j];a[pivot]=[v/scale for v in a[pivot]]
        for i in range(len(a)):
            if i!=pivot:
                scale=a[i][j];a[i]=[x-scale*y for x,y in zip(a[i],a[pivot])]
        pivot+=1
        if pivot==len(a):break
    return pivot

k=zero()
for b,lam in enumerate([1,2,3]): k[2*b][2*b+1]=F(lam);k[2*b+1][2*b]=-F(lam)
assert transpose(k)==sub(zero(),k)
assert rank(k)==6 and square_sum(k)==28

cols=[]
for i in range(N):
    for j in range(N):
        a=zero();a[i][j]=F(1)
        cols.append(upper(add(mul(a,k),mul(k,transpose(a))))+
                    upper(add(mul(transpose(a),k),mul(k,a))))
system=[list(r) for r in zip(*cols)]
rhs=upper(k)+upper(k)
r=rank(system);aug=rank([row+[value] for row,value in zip(system,rhs)])
assert r==aug==27

t=mul(k,k);hcols=[]
for i in range(N):
    for j in range(i,N):
        h=zero();h[i][j]=h[j][i]=F(1)
        hcols.append(upper(sub(mul(t,h),mul(h,t))))
hrank=rank([list(r) for r in zip(*hcols)])
assert hrank==12

identity=zero()
for i in range(N):identity[i][i]=F(1)
a=zero()
parameters=[(2,1,-3),(-1,4,2),(3,-2,7)]
for i,(p,q,rp) in enumerate(parameters):
    a[2*i][2*i]=F(p);a[2*i][2*i+1]=F(q)
    a[2*i+1][2*i]=F(rp);a[2*i+1][2*i+1]=1-F(p)
assert add(mul(a,k),mul(k,transpose(a)))==k
assert add(mul(transpose(a),k),mul(k,a))==k
gain=square_sum(add(a,transpose(a)))
formula=6+2*sum((2*p-1)**2+(q+rp)**2 for p,q,rp in parameters)
assert gain==formula==222

result={'pair':'K = Y = diag(J, 2J, 3J), J=[[0,1],[-1,0]]',
        'arithmetic':'Python fractions.Fraction, exact; not Lean checked',
        'skew_rank':rank(k),'skew_frobenius_squared':28,
        'coupled_constraint_shape':[30,36], 'coupled_constraint_rank':r,
        'augmented_rank':aug,'affine_dimension':36-r,
        'symmetric_parameter_shape':[15,21], 'symmetric_parameter_rank':hrank,
        'symmetric_parameter_nullity':21-hrank,
        'sample_parameters':parameters,'sample_identity_input_squared':6,
        'sample_identity_output_squared':int(gain),
        'general_identity':'For all three real triples (p_i,q_i,r_i), the block diagonal A_i=[[p_i,q_i],[r_i,1-p_i]] satisfies the coupled equations and ||A+A^T||_F^2 = 6 + 2 sum_i [(2p_i-1)^2+(q_i+r_i)^2] >= 6.',
        'scope':'The polynomial identity has a direct hand derivation; the script checks exact ranks and one nontrivial rational instance, not every real input.'}
out=Path(__file__).with_name('coupled-pair-check.json')
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
