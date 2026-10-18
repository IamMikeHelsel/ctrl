"""Exact Gaussian-integer self-check of the actual ordered-wedge conventions.
This is a finite regression check, not a replacement for the all-element Lean proof.
"""
from pathlib import Path
from functools import lru_cache
import json,random
B=Path(__file__).resolve().parent
Z=(0,0);O=(1,0)
def addz(x,y):return (x[0]+y[0],x[1]+y[1])
def mulz(x,y):return (x[0]*y[0]-x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def conjz(x):return (x[0],-x[1])
def scale(c,A):return {ij:mulz(c,v) for ij,v in A.items() if mulz(c,v)!=Z}
def add(A,B):
 out=A.copy()
 for ij,v in B.items():
  w=addz(out.get(ij,Z),v)
  if w==Z:out.pop(ij,None)
  else:out[ij]=w
 return out
def mul(A,B):
 rows={}
 for (j,k),v in B.items():rows.setdefault(j,[]).append((k,v))
 out={}
 for (i,j),v in A.items():
  for k,w in rows.get(j,[]):
   ij=(i,k);out[ij]=addz(out.get(ij,Z),mulz(v,w))
 return {ij:v for ij,v in out.items() if v!=Z}
def transpose(A):return {(j,i):v for (i,j),v in A.items()}
def adjoint(A):return {(j,i):conjz(v) for (i,j),v in A.items()}
identity={(i,i):O for i in range(128)}
basis=[tuple(j for j in range(7) if mask&(1<<j)) for mask in range(128)]
index={s:i for i,s in enumerate(basis)}
def create(j):return {(index[tuple(sorted(T+(j,)))],c):((-1)**sum(k<j for k in T),0) for c,T in enumerate(basis) if j not in T}
def contract(j):return {(index[tuple(k for k in T if k!=j)],c):((-1)**T.index(j),0) for c,T in enumerate(basis) if j in T}
positive=[add(create(j),contract(j)) for j in range(7)]
negative=[add(create(j),scale((-1,0),contract(j))) for j in range(7)]
generators=positive+negative
K=identity
for n in negative:K=mul(K,n)
assert adjoint(K)==K and mul(K,K)==identity
@lru_cache(None)
def word(w):
 out=identity
 for i in w:out=mul(out,generators[i])
 return out
def image(terms):
 out={}
 for c,w in terms:out=add(out,scale(c,word(w)))
 return out
def bar(terms):return [(mulz(conjz(c),((-1)**len(w),0)),tuple(reversed(w))) for c,w in terms]
def product(a,b):return [(mulz(c,d),u+v) for c,u in a for d,v in b]
rng=random.Random(2026101804)
cases=[[(O,()),((0,1),(0,)),((2,-3),(8,2)),((-4,5),(13,0,7))]]
for n in range(31):
 cases.append([((rng.randrange(-5,6),rng.randrange(-5,6)),tuple(rng.randrange(14) for _ in range(rng.randrange(13)))) for _ in range(4)])
for terms in cases:
 A=image(terms)
 assert image(bar(terms))==mul(mul(K,adjoint(A)),K)
 assert image(bar(bar(terms)))==A
for a,b in zip(cases[::2],cases[1::2]):
 assert image(product(a,b))==mul(image(a),image(b))
 assert image(bar(product(a,b)))==mul(image(bar(b)),image(bar(a)))
iI=scale((0,1),identity)
assert mul(mul(K,transpose(iI)),K)!=scale((0,-1),identity)
E={(0,1):O};F={(1,0):O}
assert mul(E,F)=={(0,0):O} and mul(F,E)=={(1,1):O}
pointwise={ij:mulz(v,F.get(ij,Z)) for ij,v in E.items() if mulz(v,F.get(ij,Z))!=Z}
assert mul(E,F)!=pointwise
assert mul(mul(K,adjoint(mul(E,F))),K)!=mul(mul(mul(K,adjoint(E)),K),mul(mul(K,adjoint(F)),K))
result={'status':'PASS','arithmetic':'Gaussian integer pairs with arbitrary precision Python integers','basis':'128 ordered wedge subsets, signs from prefix length','seed':2026101804,'mixed_cases':len(cases),'terms_per_case':4,'product_pairs':16,'generator_matrices':14,'matrix_order':128,'negative_controls':{'plain_transpose_on_iI_rejected':True,'matrix_product_is_not_pointwise':True,'product_order_preservation_under_adjoint_rejected':True},'boundary':'Finite builder self-check only. The all-element actual scalar extension and bar bridge are Lean theorems. No signature or physics result is asserted.'}
(B/'exact-complex-check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
