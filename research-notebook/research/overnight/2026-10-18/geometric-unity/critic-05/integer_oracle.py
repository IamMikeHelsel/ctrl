"""Reviewer oracle: sorted wedge tuples, insertion permutations, contraction position.
No builder Python code or expected K entries are imported. All arithmetic is integer.
"""
from itertools import combinations
from pathlib import Path
import json, hashlib
B=Path(__file__).resolve().parent
basis=[t for size in range(8) for t in combinations(range(7),size)]
idx={t:i for i,t in enumerate(basis)}
n=len(basis)
def zero():return [[0]*n for _ in range(n)]
def ident():return [[int(i==j) for j in range(n)] for i in range(n)]
def trans(a):return [list(r) for r in zip(*a)]
def add(a,b):return [[x+y for x,y in zip(r,s)] for r,s in zip(a,b)]
def scale(a,k):return [[k*x for x in row] for row in a]
def matmul(a,b):
    out=zero()
    for i,row in enumerate(a):
        for k,x in enumerate(row):
            if x:
                for j,y in enumerate(b[k]):
                    if y:out[i][j]+=x*y
    return out
I=ident();N=[];P=[]
for g in range(7):
    creation=zero();contraction=zero()
    for col,t in enumerate(basis):
        if g in t:
            pos=t.index(g)
            contraction[idx[t[:pos]+t[pos+1:]]][col]=(-1)**pos
        else:
            unsorted=(g,)+t
            inversions=sum(unsorted[a]>unsorted[b] for a in range(len(unsorted)) for b in range(a+1,len(unsorted)))
            creation[idx[tuple(sorted(unsorted))]][col]=(-1)**inversions
    N.append(add(creation,scale(contraction,-1)))
    P.append(add(creation,contraction))
# Product is assembled by matrix multiplication in source order, not the target formula.
K=I
for generator in N:K=matmul(K,generator)
checks={};entry_checks=0
def eq(name,a,b):
    global entry_checks
    assert a==b,name
    checks[name]=n*n;entry_checks+=n*n
for g in range(7):
    eq('negative-square-'+str(g),matmul(N[g],N[g]),scale(I,-1))
    eq('positive-square-'+str(g),matmul(P[g],P[g]),I)
for g in range(7):
    for h in range(g+1,7):eq(f'negative-anticommutation-{g}-{h}',add(matmul(N[g],N[h]),matmul(N[h],N[g])),zero())
for g in range(7):
    for h in range(7):eq(f'mixed-anticommutation-{g}-{h}',add(matmul(P[g],N[h]),matmul(N[h],P[g])),zero())
actual=[]
for col,t in enumerate(basis):
    nonzero=[(basis[row],K[row][col]) for row in range(n) if K[row][col]]
    complement=tuple(g for g in range(7) if g not in t)
    sign=(-1)**sum(7-g for g in t)
    assert nonzero==[(complement,sign)],(t,nonzero,sign)
    actual.append({'subset':t,'actual_image':complement,'actual_coefficient':sign})
D=zero()
for i,t in enumerate(basis):D[i][i]=1 if 0 not in t else -1
U=add(I,matmul(K,D));UT=trans(U)
eq('K-symmetric',trans(K),K)
eq('K-square',matmul(K,K),I)
eq('D-K-anticommutes',matmul(D,K),scale(matmul(K,D),-1))
eq('U-left-doubled-inverse',matmul(UT,U),scale(I,2))
eq('U-right-doubled-inverse',matmul(U,UT),scale(I,2))
eq('actual-congruence',matmul(matmul(UT,K),U),scale(D,2))
eq('actual-eigen-columns',matmul(K,U),matmul(U,D))
reverse=I
for generator in reversed(N):reverse=matmul(reverse,generator)
eq('reversed-product-is-negative',reverse,scale(K,-1))
positive=sum(row[i]==1 for i,row in enumerate(D));negative=sum(row[i]==-1 for i,row in enumerate(D))
assert (positive,negative)==(64,64)
# Complex vectors are pairs of arbitrary integers, never floating complex numbers.
def gauss_add(z,w):return(z[0]+w[0],z[1]+w[1])
def gauss_mul(z,w):return(z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0])
def gauss_conj(z):return(z[0],-z[1])
def action(a,v):return[(sum(x*z[0] for x,z in zip(row,v)),sum(x*z[1] for x,z in zip(row,v))) for row in a]
def pairing(v,a,w):
    aw=action(a,w);value=(0,0)
    for z,t in zip(v,aw):value=gauss_add(value,gauss_mul(gauss_conj(z),t))
    return value
complex_tests=[]
for seed in range(32):
    v=[((seed+3)*(i+1)%17-8,(seed+5)*(i+2)%19-9) for i in range(n)]
    w=[((seed+7)*(i+5)%23-11,(seed+11)*(i+7)%29-14) for i in range(n)]
    left=pairing(action(U,v),K,action(U,w));right=pairing(v,scale(D,2),w)
    assert left==right
    complex_tests.append({'seed':seed,'sesquilinear_pair':left})
# Mutants: explain a concrete wrong value, beyond mere failing Boolean output.
empty=idx[()];full=idx[tuple(range(7))];single=idx[(0,)];single_c=idx[tuple(range(1,7))]
mutants={
 'omit-complement':{'entry':[empty,empty],'actual':K[empty][empty],'false_target':1},
 'omit-sign':{'entry':[single_c,single],'actual':K[single_c][single],'false_target':1},
 'reverse-generators':{'entry':[full,empty],'actual':reverse[full][empty],'false_target':1},
 'omit-half-inverse':{'entry':[empty,empty],'actual':matmul(UT,U)[empty][empty],'false_target':1},
 'assume-positive-form':{'entry':[single,single],'actual':matmul(matmul(UT,K),U)[single][single],'false_target':2},
 'D-and-K-swap':{'entry':[empty,empty],'actual':matmul(matmul(U,K),UT)[empty][empty],'false_target':2}}
for m in mutants.values():assert m['actual']!=m['false_target']
# I+K kills 64 disjoint, nonzero, independently supported vectors.
projector=add(I,K);kernel_vectors=0
for t in basis:
    if 0 not in t:
        v=[0]*n;v[idx[t]]=1
        col=idx[t]
        for row in range(n):v[row]-=K[row][col]
        assert any(v)
        assert all(sum(a*x for a,x in zip(row,v))==0 for row in projector)
        kernel_vectors+=1
assert kernel_vectors==64
out={'status':'PASS','basis_size':n,'construction':'sorted exterior tuples; permutation insertion and positional contraction','actual_basis_actions_checked':len(actual),'matrix_entry_equalities_checked':entry_checks,'matrix_identities':checks,'half_counts':[positive,negative],'complex_integer_pair_tests':complex_tests,'omitted_D_disjoint_kernel_vectors':kernel_vectors,'mutants':mutants,'actual_actions':actual,'scope':'Exact finite independent oracle; not a substitute for Lean or physical evidence.'}
(B/'integer-oracle-result.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['status','basis_size','actual_basis_actions_checked','matrix_entry_equalities_checked','half_counts','omitted_D_disjoint_kernel_vectors']}))
