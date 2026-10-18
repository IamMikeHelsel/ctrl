"""Exact-rational partition probe using the Lean-proved coefficient enclosures.
Outputs candidate certificate bounds, not a proof of the generated trace.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json,math,time
HERE=Path(__file__).resolve().parent
pt=lambda x:(F(x),F(x))
add=lambda a,b:(a[0]+b[0],a[1]+b[1])
neg=lambda a:(-a[1],-a[0])
sub=lambda a,b:add(a,neg(b))
def mul(a,b):
 v=[x*y for x in a for y in b];return min(v),max(v)
def sq(a):return (F(0) if a[0]<=0<=a[1] else min(a[0]**2,a[1]**2),max(a[0]**2,a[1]**2))
clip=lambda a:tuple(max(F(-1),min(F(1),v)) for v in a)
D=2**44
rnd=lambda a:(F(math.floor(a[0]*D),D),F(math.ceil(a[1]*D),D))
def energy(z):
 x,v,a=z
 return add(add(mul(pt(F(38,5)),sq(add(add(x,mul(pt(F(257,190)),v)),mul(pt(F(25,38)),a)))),mul(pt(F(29628,2375)),sq(add(v,mul(pt(F(20465,29628)),a))))),mul(pt(F(1391479,740700)),sq(a)))[1]
def run(n):
 t=time.monotonic();bounds=[(F(99,100),F(101,100)),(F(49,100),F(51,100)),(F(-1,100),F(1,100))]
 init=[[(lo+(hi-lo)*F(k,n),lo+(hi-lo)*F(k+1,n)) for k in range(n)] for lo,hi in bounds]
 best=F(0);coarse=True
 for row in json.loads((HERE/'coefficient-data.json').read_text()):
  E,B,C=[tuple(map(F,row[k])) for k in ['E','B','C']]
  for z in product(*init):
   for step in range(25):
    coarse &= abs(z[0][0])<=F(3,2) and abs(z[0][1])<=F(3,2) and all(abs(q)<=1 for zz in z[1:] for q in zz)
    x,v,a=z;u=clip(neg(add(add(x,mul(pt(3),v)),mul(pt(2),a))))
    z=list(map(rnd,[add(add(add(x,mul(pt(F(1,20)),v)),mul(C,a)),mul(sub(pt(F(1,800)),C),u)),add(add(v,mul(B,a)),mul(sub(pt(F(1,20)),B),u)),add(mul(E,a),mul(sub(pt(1),E),u))]))
   best=max(best,energy(z))
 return {'subdivisions':n,'cells':16*n**3,'energy_upper_exact':str(best),'energy_upper':float(best),'energy_pass':best<=12,'coarse_path_conditions':coarse,'seconds':time.monotonic()-t}
if __name__=='__main__':
 out=[run(n) for n in (1,2,4)];(HERE/'cover-probe.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
