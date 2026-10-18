"""Exact integer ordered-wedge check. This is not the Lean representation proof."""
from pathlib import Path
import json
B=Path(__file__).resolve().parent
subsets=[tuple(j for j in range(7) if mask&(1<<j)) for mask in range(128)]
index={s:i for i,s in enumerate(subsets)}
zero=tuple((None,0) for _ in subsets)
one=tuple((i,1) for i in range(128))
def neg(A):return tuple((r,-s) for r,s in A)
def transpose(A):
 out=list(zero)
 for col,(row,sign) in enumerate(A):
  if row is not None:
   assert out[row]==(None,0)
   out[row]=(col,sign)
 return tuple(out)
def mul(A,B):
 out=[]
 for r,s in B:
  if r is None:out.append((None,0));continue
  rr,ss=A[r]
  out.append((rr,s*ss) if rr is not None else (None,0))
 return tuple(out)
def plus_disjoint(A,B):
 out=[]
 for a,b in zip(A,B):
  assert a[0] is None or b[0] is None
  out.append(b if a[0] is None else a)
 return tuple(out)
def creation(j):
 out=[]
 for T in subsets:
  if j in T:out.append((None,0));continue
  out.append((index[tuple(sorted(T+(j,)))],(-1)**sum(k<j for k in T)))
 return tuple(out)
def contraction(j):
 out=[]
 for T in subsets:
  if j not in T:out.append((None,0));continue
  out.append((index[tuple(k for k in T if k!=j)],(-1)**T.index(j)))
 return tuple(out)
C=[creation(j) for j in range(7)];A=[contraction(j) for j in range(7)]
P=[plus_disjoint(c,a) for c,a in zip(C,A)];N=[plus_disjoint(c,neg(a)) for c,a in zip(C,A)]
for j in range(7):
 assert transpose(C[j])==A[j]
 assert transpose(P[j])==P[j]
 assert transpose(N[j])==neg(N[j])
 assert mul(P[j],P[j])==one and mul(N[j],N[j])==neg(one)
K=one
for n in N:K=mul(K,n)
assert transpose(K)==K and mul(K,K)==one
G=P+N
for g in G:assert mul(mul(K,transpose(g)),K)==neg(g)
assert all(r==127-i for i,(r,s) in enumerate(K))
Kr=one
for n in reversed(N):Kr=mul(Kr,n)
assert Kr==neg(K)
assert all(mul(mul(Kr,transpose(g)),Kr)==neg(g) for g in G)
assert transpose(P[0])!=neg(P[0])
assert mul(plus_disjoint(C[0],A[0]),plus_disjoint(C[0],A[0]))!=neg(one)
assert mul(K,transpose(P[0]))!=neg(P[0])
# H=i*K*D with D the actual exterior parity. Since H is pure imaginary,
# Hermitian H is equivalent to real KD being skew-transpose.
D=tuple((i,(-1)**len(T)) for i,T in enumerate(subsets));KD=mul(K,D)
assert transpose(KD)==neg(KD)
for i in range(14):
 for j in range(i+1,14):
  bivector=mul(G[i],G[j])
  assert mul(transpose(bivector),KD)==neg(mul(KD,bivector))
failed=[j for j,g in enumerate(G) if mul(transpose(g),KD)!=neg(mul(KD,g))]
assert failed==list(range(14))
ratios={s/t for (r,s),(q,t) in zip(KD,K)}
assert ratios=={-1,1}
result={'status':'PASS','arithmetic':'Python arbitrary precision integer signed partial-permutation columns',
 'basis':'increasing tuples of occupied Fin 7 indices, bit-mask enumeration; signs count the ordered prefix',
 'basis_columns':128,'creation_contraction_pairs':7,'actual_generator_checks':14,'bivector_checks':91,
 'K_symmetric':True,'K_square_identity':True,'K_maps_complementary_subsets':True,
 'reversed_K_is_negative_K':True,'reversed_K_preserves_adjoint':True,
 'negative_controls':{'positive_euclidean_skew_fails':True,'plus_negative_square_fails':True,'omitted_right_K_fails':True},
 'spin_only_witness':{'form':'i K D with D exterior parity','Hermitian':True,'bivector_invariant':True,
 'not_a_complex_scalar_multiple_of_K':True,'full_vector_skew_fails_for_generators':failed},
 'boundary':'Exact finite convention checks only. The actual all-element real representation bridge is proved in Lean. No complex representation, signature theorem or GU physics follows.'}
(B/'convention-check.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: actual ordered-wedge conventions, K signs, and Spin-only witness')
