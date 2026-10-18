"""Exact circulant-blowup diagnostic; no large adjacency matrix is allocated."""
from fractions import Fraction as F
from math import lcm
from pathlib import Path
import hashlib,json
I=F(2,47); R=F(1,40); c=F(133,160); y=1/(2*c);x=1-y
j=F(71,1880);q=I-j;b=y-F(1,2);mu=2*j/y;dx=2*q/x
N=2*lcm(y.denominator,mu.denominator,dx.denominator)
ny=int(y*N);nx=int(x*N);dy=int(mu*N);degree_x=int(dx*N)
assert ny%2==nx%2==N%2==0
assert F(ny,N)==y and F(nx,N)==x and F(dy,N)==mu and F(degree_x,N)==dx
assert 0<dy<=ny//2 and 0<degree_x<=nx//2
assert F(ny*dy,2*N*N)==j and F(nx*degree_x,2*N*N)==q
removed=ny-N//2
assert 0<=removed<=ny//2
restricted=F(ny*dy//2-dy*removed,N*N)
assert restricted==j-b*mu and restricted>R
assert mu>b and c*c*j>R
Q=x*(F(1,2)-x)/2
assert Q+q>R
# Small version checks the finite circulant degree and exact deletion identity.
def support(m,d):return [(i,m+(i+s)%m) for i in range(m) for s in range(d)]
E=support(5,2);deg=[0]*10
for a,z in E:deg[a]+=1;deg[z]+=1
assert deg==[2]*10
from itertools import combinations
best=999
for removed_small in combinations(range(10),3):
 T=set(removed_small);inside=sum(a in T and z in T for a,z in E)
 left=sum(a not in T and z not in T for a,z in E)
 assert left==len(E)-2*len(T)+inside
 best=min(best,left)
assert best==len(E)-2*3
result={'scope':'exact parameter and finite-construction arithmetic; written universal counting proof is separate and awaits independent review','parameters':{k:str(v) for k,v in dict(I=I,R=R,c=c,x=x,y=y,j=j,q=q,b=b,mu=mu,degree_x_mass=dx).items()},'finite_graph':{'order':N,'Y_order':ny,'X_order':nx,'Y_degree':dy,'X_degree':degree_x,'removed_from_Y':removed,'half_order':N//2,'construction':'Disjoint X and Y bipartite regular circulants; each uses two equal parts and modular shifts 0<=s<degree.'},'costs':{'Y_restricted_half_optimum':str(restricted),'Y_restricted_gap':str(restricted-R),'uniform':str(c*c*j),'completion_envelope':str(Q+q),'global_half_optimum':'0','chosen_internal_cut':str(q+j),'maximum_cut_internal_cost':'0'},'small_control':{'vertices':10,'degree':2,'removed_vertices':3,'minimum_remaining_edges':best},'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
Path(__file__).with_name('result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
