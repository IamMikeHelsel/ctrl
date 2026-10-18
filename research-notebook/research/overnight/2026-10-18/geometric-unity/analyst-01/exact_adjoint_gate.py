"""Exact integer preflight. This is evidence, not a Lean proof.

Solve all linear equations G_a^T H + H G_a = 0 by signed union-find.
Each equation relates two entries by a sign. A negative cycle forces its
whole component to zero over a characteristic-zero field. Remaining
components have one free scalar each. No floating point is used.
"""
from pathlib import Path
from collections import Counter
import json,hashlib
N=128

def gamma(j,negative):
    return tuple((col^(1<<j), (-1)**((col&((1<<j)-1)).bit_count()) *
                  (-1 if negative and col&(1<<j) else 1)) for col in range(N))
def mul(a,b): return tuple((a[j][0],s*a[j][1]) for j,s in b)
def tr(a):
    out=[None]*N
    for col,(row,s) in enumerate(a):out[row]=(col,s)
    return tuple(out)
def smul(a,s):return tuple((r,s*t) for r,t in a)
I=tuple((i,1) for i in range(N))
G=[gamma(i,False) for i in range(7)]+[gamma(i,True) for i in range(7)]
K=I
for g in G[7:]:K=mul(K,g)

class SignedUF:
    def __init__(self,n):self.p=list(range(n));self.s=[1]*n;self.bad=[False]*n;self.size=[1]*n
    def find(self,i):
        if self.p[i]!=i:
            p=self.p[i];r,s=self.find(p);self.p[i]=r;self.s[i]*=s
        return self.p[i],self.s[i]
    def relate(self,a,b,sign):
        # x_a = sign*x_b; x_a=sa*x_ra and x_b=sb*x_rb.
        ra,sa=self.find(a);rb,sb=self.find(b);t=sign*sa*sb
        if ra==rb:
            if t==-1:self.bad[ra]=True
            return
        if self.size[ra]<self.size[rb]:ra,rb=rb,ra
        self.p[rb]=ra;self.s[rb]=t;self.size[ra]+=self.size[rb]
        self.bad[ra]=self.bad[ra] or self.bad[rb]

uf=SignedUF(N*N);equations=0
for g in G:
    for r,(gr,sr) in enumerate(g):
        for c,(gc,sc) in enumerate(g):
            uf.relate(gr*N+c,r*N+gc,-sc*sr);equations+=1
components={}
for i in range(N*N):
    root,s=uf.find(i);components.setdefault(root,[]).append((i,s))
free=[root for root in components if not uf.bad[root]]
assert len(free)==1
root=free[0]
H=[[0]*N for _ in range(N)]
for i,s in components[root]:H[i//N][i%N]=s
k00=next((r,c,s) for c,(r,s) in enumerate(K))
r,c,s=k00;scale=H[r][c]*s
for c,(r,s) in enumerate(K):assert H[r][c]==scale*s
assert sum(v!=0 for row in H for v in row)==N
# Full equation residual, separate from the union-find relation path.
assert all(sr*H[gr][c]+sc*H[r][gc]==0
           for g in G for r,(gr,sr) in enumerate(g) for c,(gc,sc) in enumerate(g))
assert tr(K)==K and mul(K,K)==I
pairs=[(j,K[j][0],K[j][1]) for j in range(N) if j<K[j][0]]
assert len(pairs)==64
# u_j +/- s_j*u_complement has K-norm +/-2; supports of distinct pairs disjoint.
assert all(k==j^127 and K[k]==(j,s) for j,k,s in pairs)
assert len(set(x for j,k,s in pairs for x in (j,k)))==N
congruence=[]
for j,k,s in pairs:
    congruence.append({'positive_column':[[j,1],[k,s]],'negative_column':[[j,1],[k,-s]]})
# Wrong Euclidean metric fails every positive-square skew equation.
wrong_euclidean=[i for i,g in enumerate(G) if tr(g)!=smul(g,-1)]
# Changing negative generators to creation+contraction breaks their square.
wrong_negative_squares=[j for j in range(7) if mul(gamma(j,False),gamma(j,False))!=smul(I,-1)]
out={'status':'pass','arithmetic':'exact Python integers','dimension':N,
     'linear_equations':equations,'variables':N*N,'connected_components':len(components),
     'forced_zero_components':sum(uf.bad[r] for r in components),
     'free_components':len(free),'solution_space_complex_dimension':1,
     'free_support_entries':len(components[root]),
     'form_space':'H=c*K; Hermitian H forces c real, nondegenerate requires c != 0',
     'K_real_symmetric':True,'K_square_identity':True,
     'integer_congruence':'U^T K U = diag(2*I64,-2*I64)',
     'signature':[64,64], 'negative_controls':{'Euclidean_form_failed_generators':wrong_euclidean,
         'positive_substitution_failed_negative_squares':wrong_negative_squares},
     'boundary':'No Lean proof of matrix-coordinate bridge, faithfulness, adjoint compatibility, or uniqueness yet.'}
B=Path(__file__).resolve().parent
(B/'adjoint-congruence.json').write_text(json.dumps(congruence,indent=2)+'\n')
(B/'exact-adjoint-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
