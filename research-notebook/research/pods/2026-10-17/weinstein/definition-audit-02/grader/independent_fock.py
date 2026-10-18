"""Separate exact integer-matrix Fock checks from exterior creation/contraction."""
from itertools import combinations
import json
import numpy as np

basis=[tuple(j for j in range(7) if mask>>j&1) for mask in range(128)]
index={s:i for i,s in enumerate(basis)}
I=np.eye(128,dtype=np.int64)
create=[];ann=[]
for j in range(7):
    a=np.zeros((128,128),dtype=np.int64);b=np.zeros_like(a)
    for col,word in enumerate(basis):
        if j not in word:
            row=index[tuple(sorted((j,)+word))]
            a[row,col]=(-1)**sum(i<j for i in word)
        else:
            row=index[tuple(i for i in word if i!=j)]
            b[row,col]=(-1)**word.index(j)
    create.append(a);ann.append(b)
gamma=[a+b for a,b in zip(create,ann)]+[a-b for a,b in zip(create,ann)]
for j,g in enumerate(gamma):
    assert np.array_equal(g@g,(1 if j<7 else -1)*I)
for a,b in combinations(gamma,2):assert not np.any(a@b+b@a)
K=I.copy()
for j in range(7,14):K=K@gamma[j]
assert np.array_equal(K,K.T) and np.array_equal(K@K,I) and np.trace(K)==0
for g in gamma:assert not np.any(g.T@K+K@g)
# Exact vacuum projector, then matrix units: a wedge word times Pvac times
# the matching reversed contraction word takes one basis vector to one basis
# vector. This verifies a spanning argument without numerical matrix rank.
P=I.copy()
for a,b in zip(create,ann):P=P@b@a
expected=np.zeros_like(I);expected[0,0]=1
assert np.array_equal(P,expected)
left=[];right=[]
for word in basis:
    L=P.copy();R=P.copy()
    # Operators act on the left, so reversed construction gives sorted word.
    for j in reversed(word):L=create[j]@L
    for j in reversed(word):R=R@ann[j]
    left.append(L);right.append(R)
for row,L in enumerate(left):
    assert L[row,0]==1 and np.count_nonzero(L)==1
for col,R in enumerate(right):
    assert R[0,col]==1 and np.count_nonzero(R)==1
# L_row @ R_col is E_(row,col), with coefficient +1.
print(json.dumps({'status':'pass','dimension':128,'integer_matrix_clifford_relations':True,
 'K_symmetric_involution_trace_zero':True,'K_signature':[64,64],
 'all_generators_K_skew':True,'vacuum_projector':True,
 'all_128_creation_columns_and_contraction_rows':True,
 'all_16384_matrix_units_follow_by_outer_products':True,
 'scope':'Exact Python/NumPy integer evidence plus stated matrix-unit argument; not Lean-certified.'},indent=2))
