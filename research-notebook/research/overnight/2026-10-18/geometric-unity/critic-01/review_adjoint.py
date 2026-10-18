"""Independent exact review: ordered-wedge matrices and signed-graph traversal.

Does not import the analyst's signed union-find or gamma constructor.
All matrix operations are on small bounded integers. No eigenvalue calculation.
"""
from pathlib import Path
from collections import deque
import json, hashlib
import numpy as np

B=Path(__file__).resolve().parent
A=B.parent/'analyst-01'
n=7
N=2**n
I=np.eye(N,dtype=np.int64)
subsets=[tuple(j for j in range(n) if mask & (1<<j)) for mask in range(N)]
index={s:i for i,s in enumerate(subsets)}
creation=[]
annihilation=[]
for j in range(n):
    c=np.zeros((N,N),dtype=np.int64)
    a=np.zeros((N,N),dtype=np.int64)
    for col,s in enumerate(subsets):
        if j not in s:
            out=tuple(sorted((j,)+s))
            swaps=out.index(j)
            c[index[out],col]=1 if swaps%2==0 else -1
        else:
            swaps=s.index(j)
            out=tuple(k for k in s if k!=j)
            a[index[out],col]=1 if swaps%2==0 else -1
    assert np.array_equal(a,c.T)
    assert np.array_equal(a@a,0*I) and np.array_equal(c@c,0*I)
    assert np.array_equal(a@c+c@a,I)
    creation.append(c);annihilation.append(a)
G=[a+c for a,c in zip(annihilation,creation)]+[c-a for a,c in zip(annihilation,creation)]
for i,g in enumerate(G):
    assert np.array_equal(g@g,I if i<n else -I)
    for j,h in enumerate(G):
        assert np.array_equal(g@h+h@g, (2 if i<n else -2)*I if i==j else 0*I)

# Build each equality from the two nonzero terms of (G^T H+HG)[r,c].
# Store graph edges; then solve by breadth-first propagation, not union-find.
adj=[[] for _ in range(N*N)]
equations=0
for g in G:
    entries=[(int(np.flatnonzero(g[:,c])[0]),int(g[np.flatnonzero(g[:,c])[0],c])) for c in range(N)]
    for r,(rr,sr) in enumerate(entries):
        for c,(cc,sc) in enumerate(entries):
            x=rr*N+c;y=r*N+cc;sgn=-sr*sc
            adj[x].append((y,sgn));adj[y].append((x,sgn));equations+=1
value={}
components=[]
for start in range(N*N):
    if start in value:continue
    value[start]=1;q=deque([start]);nodes=[];inconsistent=False
    while q:
        x=q.popleft();nodes.append(x)
        for y,s in adj[x]:
            wanted=s*value[x]
            if y in value:
                inconsistent |= value[y]!=wanted
            else:value[y]=wanted;q.append(y)
    components.append((nodes,inconsistent))
free=[nodes for nodes,bad in components if not bad]
assert len(components)==128 and len(free)==1
assert all(len(nodes)==128 for nodes,_ in components)
H=np.zeros((N,N),dtype=np.int64)
for node in free[0]:H.flat[node]=value[node]
for g in G:assert np.array_equal(g.T@H+H@g,0*I)
assert all((node//N)^(node%N)==127 for node in free[0])
K=I.copy()
for g in G[n:]:K=K@g
assert np.array_equal(K,K.T) and np.array_equal(K@K,I)
assert np.array_equal(H,K) or np.array_equal(H,-K)
for g in G:assert np.array_equal(g.T@K+K@g,0*I)

# Check every provided coordinate of the analyst's explicit congruence.
pairs=json.loads((A/'adjoint-congruence.json').read_text())
assert len(pairs)==64
U=np.zeros((N,N),dtype=np.int64)
for i,pair in enumerate(pairs):
    for row,entry in pair['positive_column']:U[row,i]=entry
    for row,entry in pair['negative_column']:U[row,64+i]=entry
D=2*I.copy();D[64:,64:]*=-1
assert np.array_equal(U.T@K@U,D)
assert np.array_equal(U.T@U,2*I) and np.array_equal(U@U.T,2*I)
# Thus U is invertible over R, with inverse U^T/2, and Sylvester inertia applies.

negatives={
 'euclidean_form_failed_generators':[i for i,g in enumerate(G) if np.any(g.T+g)],
 'positive_replacement_breaks_negative_square':all(np.array_equal(g@g,I) for g in G[:n]),
 'mixed_factor_two_false':all(not np.array_equal(a@c+c@a,2*I) for a,c in zip(annihilation,creation)),
 'missing_congruence_column_breaks_invertibility':True,
 'transpose_is_not_conjugate_transpose_on_i_identity':True,
}
broken=U.copy();broken[:,0]=0
assert not np.array_equal(broken.T@broken,2*I)
# Exact Gaussian-integer pair: iI has K-conjugate-adjoint -iI, plain transpose +iI.
# The pair records real and imaginary coefficient matrices independently.
imaginary_identity=(0*I,I)
plain=(K@imaginary_identity[0].T@K,K@imaginary_identity[1].T@K)
dagger=(K@imaginary_identity[0].T@K,-K@imaginary_identity[1].T@K)
assert np.array_equal(plain[1],I) and np.array_equal(dagger[1],-I)

# The uniqueness premise is stronger than Spin/bivector invariance.
# D is exterior parity. The imaginary form iKD is Hermitian and invariant under
# all real bivectors but fails the all-vector skew-adjoint test.
parity=np.diag([1 if len(s)%2==0 else -1 for s in subsets]).astype(np.int64)
KD=K@parity
assert np.array_equal(KD.T,-KD)   # Therefore iKD is Hermitian.
for i in range(14):
    for j in range(i+1,14):
        bivector=G[i]@G[j]
        assert np.array_equal(bivector.T@KD+KD@bivector,0*I)
assert all(np.any(g.T@KD+KD@g) for g in G)
assert not np.array_equal(KD,K) and not np.array_equal(KD,-K)
# A one-dimensional compatible complex space restricts to a real line under H*=H:
# K is real, nonzero and symmetric, so conj(c)K=cK iff Im(c)=0.
claimed=json.loads((A/'exact-adjoint-results.json').read_text())
assert claimed['linear_equations']==equations==229376
assert claimed['free_components']==len(free)==1
assert claimed['forced_zero_components']==sum(bad for _,bad in components)==127
assert claimed['signature']==[64,64]
out={
 'status':'PASS','method':'Independent ordered-wedge matrices, breadth-first signed graph, dense exact-integer residuals and explicit congruence',
 'equations':equations,'variables':N*N,'components':len(components),'free_components':len(free),
 'forced_zero_components':sum(bad for _,bad in components),'component_size':128,
 'solution_space':'One complex free scalar, supported exactly on complementary subsets. H=cK.',
 'hermitian_restriction':'Because K is real symmetric and nonzero, H*=H iff c is real. For c nonzero signature is (64,64).',
 'congruence':'Columns are all positive columns first, then all negative columns. U^T K U=diag(2I64,-2I64).',
 'invertibility':'U^T U=UU^T=2I128, so U^{-1}=U^T/2 over the reals.',
 'negative_controls':negatives,
 'semantic_control':'Spin/bivector invariance alone has another Hermitian form iKD, with D=exterior parity. It is not a scalar multiple of K and fails all-vector skew-adjointness. The uniqueness claim requires the full vector-adjoint convention.',
 'integer_bound':'Generator/K entries are 0,+/-1, U entries 0,+/-1. Each matrix dot product has 128 terms, so int64 arithmetic is exact here.',
 'boundary':'This is a finite exact calculation and proof audit, not a Lean theorem, not a proved bridge to splitMatrix, and not faithfulness.'
}
(B/'adjoint-review.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
