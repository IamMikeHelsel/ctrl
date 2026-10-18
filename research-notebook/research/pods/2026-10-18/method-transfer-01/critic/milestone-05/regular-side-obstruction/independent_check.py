#!/usr/bin/env python3
from pathlib import Path
from fractions import Fraction as F
import hashlib,json
p=Path(__file__).parent
assert (p/'replay/result.json').read_bytes()==(p/'inputs/result.json').read_bytes()
r=json.loads((p/'inputs/result.json').read_text()); g=r['finite_graph']; N=g['order']; ny=g['Y_order']; nx=g['X_order']; dy=g['Y_degree']; dx=g['X_degree']
assert nx+ny==N and all(v%2==0 for v in (N,ny,nx))
assert 0<dy<ny//2 and 0<dx<nx//2
j=F(ny*dy,2*N*N);q=F(nx*dx,2*N*N);y=F(ny,N);mu=F(dy,N);b=y-F(1,2)
assert j==F(71,1880) and q==F(9,1880) and j+q==F(2,47)
assert mu==2*j/y and F(0)<b<y/2 and mu>b
opt=j-b*mu
assert opt-F(1,40)==F(3,150400)
# A normalized regular cycle: exact fractional, rather than only subset, deletions.
E=[(i,(i+1)%6) for i in range(6)]; w=F(1,8); degree=2*w; mass=6*w; edge=len(E)*w*w
removed=[F(1,32),F(1,16),F(3,32),F(0),F(1,32),F(1,32)]
assert sum(removed)==mass-F(1,2)
selected=[w-t for t in removed]
e=lambda z:sum(z[u]*z[v] for u,v in E)
assert e(selected)==edge-degree*sum(removed)+e(removed)
assert e(selected)>=edge-degree*sum(removed)
# Removing regularity is false: Y is a 6-vertex star, each vertex mass 1/8.
star=[(0,v) for v in range(1,6)]; jstar=F(5,64); mustar=2*jstar/mass
z=[F(0),F(0),w,w,w,w]
assert sum(z)==F(1,2)
actual=sum(z[u]*z[v] for u,v in star)
false_bound=jstar-(mass-F(1,2))*mustar
assert actual==0 and false_bound==F(5,192)>0
out={'passed':True,'frozen_entries_verified':3,'copied_replay_identical':True,'restricted_optimum':str(opt),'gap_above_one_fortieth':str(opt-F(1,40)),'independent_fractional_deletion_control':True,'irregular_negative':{'graph':'6-vertex star Y, 2 isolated X vertices, all mass 1/8','selected':'four leaves in Y','cost':str(actual),'incorrect_mean_degree_lower_bound':str(false_bound)},'scope':'Written regular counting proof reviewed separately. No large graph materialized or new Lean theorem.'}
(p/'independent-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
