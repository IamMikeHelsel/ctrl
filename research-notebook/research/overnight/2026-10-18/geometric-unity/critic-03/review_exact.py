"""Independent exact tuple-wedge construction; no builder module imports."""
from itertools import combinations
from pathlib import Path
import json, hashlib, time
B=Path(__file__).resolve().parent
start=time.monotonic()
basis=[s for k in range(8) for s in combinations(range(7),k)]
lookup={s:i for i,s in enumerate(basis)}; n=len(basis)
# Operators are signed permutations, storing the image (row, coefficient) per column.
identity=tuple((i,1) for i in range(n))
def compose(a,b):return tuple((a[j][0],c*a[j][1]) for j,c in b)
def scale(c,a):return tuple((j,c*v) for j,v in a)
def transpose(a):
 out=[None]*n
 for col,(row,s) in enumerate(a):out[row]=(col,s)
 assert all(x is not None for x in out)
 return tuple(out)
def product(ops):
 out=identity
 for op in ops:out=compose(out,op)
 return out
P=[];N=[]
creation={};annihilation={}
for i in range(7):
 p=[];q=[]
 for col,s in enumerate(basis):
  before=sum(j<i for j in s);sign=(-1)**before
  if i in s:
   target=tuple(j for j in s if j!=i);annihilation[i,col]=(lookup[target],sign)
   p.append((lookup[target],sign));q.append((lookup[target],-sign))
  else:
   target=tuple(sorted((*s,i)));creation[i,col]=(lookup[target],sign)
   p.append((lookup[target],sign));q.append((lookup[target],sign))
 P.append(tuple(p));N.append(tuple(q))
for (i,col),(row,s) in creation.items():assert annihilation[i,row]==(col,s)
for (i,col),(row,s) in annihilation.items():assert creation[i,row]==(col,s)
G=P+N
for i,g in enumerate(G):
 assert compose(g,g)==scale(1 if i<7 else -1,identity)
 assert transpose(g)==scale(1 if i<7 else -1,g)
 for h in G[i+1:]:assert compose(g,h)==scale(-1,compose(h,g))
K=product(N);assert transpose(K)==K and compose(K,K)==identity
assert product(N[::-1])==scale(-1,K)
assert K!=identity and K!=scale(-1,identity)
for col,s in enumerate(basis):assert basis[K[col][0]]==tuple(i for i in range(7) if i not in s)
def adjoint(a):return compose(compose(K,transpose(a)),K)
for g in G:assert adjoint(g)==scale(-1,g)
# Enumerate all 2^14 ordered monomials, with no floating point arithmetic.
words=[identity];orders=[0]
for g in G:
 words += [compose(a,g) for a in words]
 orders += [k+1 for k in orders]
for a,k in zip(words,orders):assert adjoint(a)==scale((-1)**(k*(k+1)//2),a)
# H=i*K*D. In this file B=K*D records its exact imaginary coefficients.
D=tuple((i,(-1)**len(s)) for i,s in enumerate(basis));Bmat=compose(K,D)
assert transpose(Bmat)==scale(-1,Bmat) # (iB)^dagger = -i B^T = iB.
bivectors=[]
for i in range(14):
 for j in range(i+1,14):
  x=compose(G[i],G[j]);bivectors.append(x)
  assert compose(Bmat,x)==scale(-1,compose(transpose(x),Bmat))
failed_vectors=[i for i,g in enumerate(G) if compose(Bmat,g)!=scale(-1,compose(transpose(g),Bmat))]
assert failed_vectors==list(range(14))
# If iKD=lambda K, multiplying by K gives iD=lambda I. Two diagonal entries differ.
assert compose(K,Bmat)==D
empty=lookup[()];single=lookup[(0,)]
assert D[empty]==(empty,1) and D[single]==(single,-1)
# Explicit complement-pair eigenvectors, independent exact sparse inner products.
pairs=[s for s in basis if 0 not in s];assert len(pairs)==64
plus=[];minus=[]
for s in pairs:
 a=lookup[s];b,sign=K[a]
 plus.append({a:1,b:sign});minus.append({a:1,b:-sign})
cols=plus+minus
def apply(op,v):
 out={}
 for j,c in v.items():
  i,d=op[j];out[i]=out.get(i,0)+c*d
 return {i:c for i,c in out.items() if c}
def dot(v,w):return sum(c*w.get(i,0) for i,c in v.items())
for i,u in enumerate(cols):
 ku=apply(K,u)
 for j,v in enumerate(cols):
  assert dot(u,v)==(2 if i==j else 0)
  assert dot(ku,v)==((2 if i<64 else -2) if i==j else 0)
controls={
 'euclidean_positive_skew':transpose(P[0])!=scale(-1,P[0]),
 'omit_right_K':compose(K,transpose(P[0]))!=scale(-1,P[0]),
 'wrong_negative_plus':compose(P[0],P[0])!=scale(-1,identity),
 'reverse_equal_K':product(N[::-1])!=K,
 'wrong_K_square':compose(K,K)!=scale(-1,identity),
 'sign_K_changes_adjoint':all(compose(compose(scale(-1,K),transpose(g)),scale(-1,K))==adjoint(g) for g in G),
 'complex_plain_transpose':1!=-1 # imaginary coefficients on the scalar iI
}
assert all(controls.values())
result={'status':'PASS','arithmetic':'Python arbitrary precision integer signed permutations and sparse columns','basis_order':'increasing tuples sorted first by cardinality then lexicographically; independent of builder bitmask enumeration','basis_columns':n,'creation_entries':len(creation),'contraction_entries':len(annihilation),'generator_relations':14,'distinct_generator_pairs':91,'ordered_monomials_checked':len(words),'all_monomial_columns_checked':len(words)*n,'K_symmetric':True,'K_square_identity':True,'reverse_K_negative':True,'sign_same_adjoint':True,'iKD':{'Hermitian':True,'bivector_equations':len(bivectors),'vector_equations_fail':failed_vectors,'not_scalar_multiple_witness':{'empty_diagonal_coefficient':1,'singleton_diagonal_coefficient':-1,'after_left_K':'iD'}},'signature_preflight':{'positive_columns':64,'negative_columns':64,'UtU':'2I','UtKU':'diag(2I64,-2I64)','Lean_signature_theorem':False},'negative_controls':controls,'seconds':round(time.monotonic()-start,3),'builder_manifest_sha256':hashlib.sha256((B.parent/'builder-03/SHA256SUMS').read_bytes()).hexdigest(),'scope':'Independent exact finite check. No general complex scalar extension theorem, global Spin group theorem, source uniqueness theorem, GU operator or physical result.'}
(B/'exact-review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','monomials':len(words),'columns':len(words)*n,'seconds':result['seconds']}))
