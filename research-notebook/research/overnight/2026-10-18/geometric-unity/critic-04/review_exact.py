"""Independent Gaussian-integer check. No builder code or floating point used."""
from itertools import combinations
from pathlib import Path
import json, random, hashlib, time
D=Path(__file__).resolve().parent;start=time.monotonic()
# Tuple wedge coordinates, sorted by grade, are deliberately not bitmask order.
basis=[v for k in range(8) for v in combinations(range(7),k)];index={v:i for i,v in enumerate(basis)};N=len(basis)
Z=(0,0);ONE=(1,0)
def add(x,y):return (x[0]+y[0],x[1]+y[1])
def mul(x,y):return (x[0]*y[0]-x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def conj(x):return (x[0],-x[1])
def plus(A,B):
 out=dict(A)
 for ij,z in B.items():
  w=add(out.get(ij,Z),z)
  if w==Z:out.pop(ij,None)
  else:out[ij]=w
 return out

def scale(c,A):return {ij:mul(c,z) for ij,z in A.items() if mul(c,z)!=Z}
def times(A,B):
 arows={}
 for (i,k),v in A.items():arows.setdefault(k,[]).append((i,v))
 C={}
 for (k,j),w in B.items():
  for i,v in arows.get(k,[]):
   key=(i,j);z=add(C.get(key,Z),mul(v,w))
   if z!=Z:C[key]=z
   else:C.pop(key,None)
 return C

def transpose(A):return {(j,i):z for (i,j),z in A.items()}
def dagger(A):return {(j,i):conj(z) for (i,j),z in A.items()}
Id={(i,i):ONE for i in range(N)}
def product(ops):
 out=Id
 for A in ops:out=times(out,A)
 return out
Cs=[];As=[];Gp=[];Gn=[]
for r in range(7):
 C={};A={}
 for j,w in enumerate(basis):
  sign=(-1)**sum(k<r for k in w)
  if r in w:A[index[tuple(k for k in w if k!=r)],j]=(sign,0)
  else:C[index[tuple(sorted(w+(r,)))],j]=(sign,0)
 assert transpose(C)==A
 Cs.append(C);As.append(A);Gp.append(plus(C,A));Gn.append(plus(C,scale((-1,0),A)))
G=Gp+Gn
for i,g in enumerate(G):
 assert times(g,g)==scale((1 if i<7 else -1,0),Id)
 for h in G[:i]:assert times(g,h)==scale((-1,0),times(h,g))
K=product(Gn)
assert dagger(K)==K and times(K,K)==Id
assert product(Gn[::-1])==scale((-1,0),K)
for j,I in enumerate(basis):
 J=tuple(i for i in range(7) if i not in I)
 assert K[index[J],j]==((-1)**sum(7-i for i in I),0)
def form(A):return times(times(K,dagger(A)),K)
for g in G:assert form(g)==scale((-1,0),g)
# Domain terms retain complex coefficients and noncommuting ordered generator words.
cache={():Id}
def word(w):
 if w not in cache:cache[w]=product([G[i] for i in w])
 return cache[w]
def rho(terms):
 ans={}
 for c,w in terms:ans=plus(ans,scale(c,word(w)))
 return ans

def bar(terms):return [(mul(conj(c),((-1)**len(w),0)),tuple(reversed(w))) for c,w in terms]
def tensor_product(x,y):return [(mul(c,d),u+v) for c,u in x for d,v in y]
rng=random.Random(104729)
samples=[ [((0,1),())], [((2,3),(0,7)),((-5,1),(13,2,9))] ]
for k in range(46):
 samples.append([((rng.randint(-4,4),rng.randint(-4,4)),tuple(rng.randrange(14) for _ in range(rng.randrange(0,8)))) for _ in range(2+k%6)])
for terms in samples:
 A=rho(terms)
 assert rho(bar(terms))==form(A)
 assert rho(bar(bar(terms)))==A
 assert form(form(A))==A
 assert rho([((0,1),())]+terms)==plus(scale((0,1),Id),A)
product_checks=0
for k in range(24):
 x=samples[2*k];y=samples[2*k+1];xy=tensor_product(x,y)
 assert rho(xy)==times(rho(x),rho(y))
 assert rho(bar(xy))==times(rho(bar(y)),rho(bar(x)))
 assert form(times(rho(x),rho(y)))==times(form(rho(y)),form(rho(x)))
 product_checks+=1
# Explicit real matrix units from the accepted wedge conventions, now with complex coefficients.
P=product([times(As[i],Cs[i]) for i in range(7)])
assert P=={(index[()],index[()]):ONE}
unit_samples=[]
for k in range(128):
 I=basis[k];J=basis[(37*k+13)%128]
 U=times(times(product([Cs[i] for i in I]),P),product([As[j] for j in reversed(J)]))
 expected={(index[I],index[J]):ONE}
 assert U==expected
 c=(2*k-127,3-k)
 assert scale(c,U)=={(index[I],index[J]):c}
 unit_samples.append((I,J))
# Arbitrary complex matrices test the involution outside monomial images.
A={(i,j):(i-2*j,3*i+j+1) for i in range(N) for j in range(N)}
assert form(form(A))==A
E={(0,1):ONE};F={(1,0):ONE}
controls={
 'ordinary_transpose_on_imaginary_identity':times(times(K,transpose(scale((0,1),Id))),K)!=rho(bar([((0,1),())])),
 'complex_scalar_conjugated_in_forward_map':rho([((0,1),())])!=scale((0,-1),Id),
 'pointwise_is_not_matrix_product':times(E,F)!={ij:mul(z,F.get(ij,Z)) for ij,z in E.items() if mul(z,F.get(ij,Z))!=Z},
 'unreversed_bar_product':rho(bar(tensor_product([((1,0),(0,))],[((1,0),(7,))])))!=times(rho(bar([((1,0),(0,))])),rho(bar([((1,0),(7,))]))),
 'identity_is_not_skew':form(Id)!=scale((-1,0),Id),
 'wrong_K_square':times(K,K)!=scale((-1,0),Id),
 'reverse_K_has_same_two_sided_adjoint':times(times(scale((-1,0),K),dagger(A)),scale((-1,0),K))==form(A)}
assert all(controls.values())
result={'status':'PASS','arithmetic':'arbitrary precision Gaussian integers; sparse matrices; no builder module imported','basis_order':'increasing tuples, sorted by grade and lexicographically','dimension':N,'generator_pairs':91,'mixed_complex_examples':len(samples),'mixed_products':product_checks,'explicit_matrix_units':len(unit_samples),'K_complement_sign_cases':128,'dense_arbitrary_matrix_entries':len(A),'negative_controls':controls,'seconds':round(time.monotonic()-start,3),'source_conventions':'Cs are left creation on increasing wedge words; As are contraction; G+=C+A; G-=C-A; K=G-0...G-6; bar conjugates scalar and reverses/negates vector word','scope':'Independent finite regression checks; not the general Lean theorem, full complex Clifford universal property, signature or physics.'}
(D/'exact-review.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
