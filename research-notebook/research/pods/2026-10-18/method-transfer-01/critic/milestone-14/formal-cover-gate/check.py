#!/usr/bin/env python3
"""Exact statement-gate controls. No Lean or generic interval soundness claim."""
from fractions import Fraction as F
from pathlib import Path
from collections import Counter
import json,hashlib
P=Path(__file__).resolve().parent
R=F(251,10000); I=F(2,47); lo=F(767,1000); hi=F(22,25)
def comp(c):
 x=1-1/(2*c)
 return F(3,2)*x*x-F(5,4)*x+F(9,32) if c<=F(4,5) else x*(F(1,2)-x)/2
def moments(c,j,R,theta):
 y=1/(2*c); m=4*c*j; b=y-F(1,2); K=4*R+1
 a=(j-R)/b; L0=8*R*(y-m)-2*m; L1=a-2*m
 L=L0+theta*(L1-L0); C=j-4*R*(y-m)**2-m*m
 A=C+(L-L0)**2/(4*K); H=(a-L)**2/4+L*m
 assert A==C+theta**2*(L1-L0)**2/(4*K)
 assert H==a*m-m*m+(1-theta)**2*(L1-L0)**2/4
 return {'A':A,'H':H,'L':L,'Hmin':a*m-m*m,'mu':m,'b':b,'y':y}
a=R+F(1,4)-I
poly=lambda c:a*c*c-F(3,8)*c+R+F(1,8)
margins={'low_uniform':R-I*lo*lo,'high_at_left':poly(hi),'high_derivative_at_left':2*a*hi-F(3,8),'high_leading':a,'middle_c':lo,'middle_b':1/(2*hi)-F(1,2),'K':4*R+1,'completion_domain':lo-F(3,4)}
assert margins['low_uniform']==F(1561,23500000)
assert margins['high_at_left']==F(54123,293750000)
assert margins['high_derivative_at_left']==F(201409,5875000)
assert a==F(109297,470000)
assert all(v>0 for v in margins.values())
x=F(3,8)
joinlow=F(3,2)*x*x-F(5,4)*x+F(9,32); joinhigh=x*(F(1,2)-x)/2
assert joinlow==joinhigh==F(3,128)
# Exact controls of the written generic high-exterior polynomial identity.
for c in [hi,F(9,10),F(1)]:
 assert poly(c)==poly(hi)+(2*a*hi-F(3,8))*(c-hi)+a*(c-hi)**2
 assert (1+c*c)*R-c*c*(I+comp(c))==poly(c)
 assert comp(c)+I-R/(c*c)==R-poly(c)/(c*c)<R
# Matched fixed target and scalar point, not a realized graph.
c=F(5347,6400); j=F(895,24064)
m0=moments(c,j,R,F(0)); m1=moments(c,j,R,F(1))
assert c*c*j>R and comp(c)+I-j>R
assert m0['H']>0 and m1['A']<0 and m1['H']<0
matched={'c':c,'j':j,'uniform_gap':c*c*j-R,'completion_gap':comp(c)+I-j-R,'theta0':m0,'theta1':m1}
# A changed .025 selector is actually false, including all rational slopes.
c=F(133,160);j=F(71,1880); r0=F(1,40)
obs=moments(c,j,r0,F(1))
assert obs['Hmin']==F(1255919,50895360000)>0
assert c*c*j>r0 and comp(c)+I-j>r0
assert obs['b']<obs['mu']<obs['y']
obstruction={'c':c,'j':j,'target':r0,'uniform_gap':c*c*j-r0,'completion_gap':comp(c)+I-j-r0,'Hmin':obs['Hmin']}
# A degree-dependent slope does NOT cancel in expectation.
d=(F(1,4),F(3,4));mu=F(1,2);L=(-1,1)
assert sum(d)/2==mu
variable_mean=sum(Li*(di-mu) for Li,di in zip(L,d))/2
assert variable_mean==F(1,4)>0
# Sound square enclosure must allow zero inside an interval that straddles it.
assert min(F(-1)**2,F(2)**2)==1>F(0)**2
# Independently check the actual tree data's exact child boxes and closed union.
raw=(P/'inputs/E5-certificate.json').read_bytes()
assert hashlib.sha256(raw).hexdigest()=='130162c84e4e7c899cf873e40cbad19bccad8d836afe86013beea700fd2e8dfb'
data=json.loads(raw);nodes=data['nodes'];seen=set();counts=Counter();thetas=Counter();splits=Counter()
def interval(vals): return tuple(map(F,vals))
def walk(i,cb,jb):
 assert i not in seen;seen.add(i);n=nodes[i]
 assert interval(n['c'])==cb and interval(n['j'])==jb
 if n['method']=='split':
  assert len(n['children'])==2
  a,b=n['children'];mid=F(n['midpoint']);axis=n['axis'];splits[axis]+=1
  if axis=='c':
   assert cb[0]<mid<cb[1]
   walk(a,(cb[0],mid),jb);walk(b,(mid,cb[1]),jb)
  else:
   assert axis=='j' and jb[0]<mid<jb[1]
   walk(a,cb,(jb[0],mid));walk(b,cb,(mid,jb[1]))
 else:
  assert n['method'] in ['uniform','completion','free_moment']
  counts[n['method']]+=1
  if n['method']=='free_moment':thetas[n['theta']]+=1
walk(0,(lo,hi),(F(0),I))
assert len(seen)==len(nodes)==1743
assert dict(counts)=={'uniform':53,'completion':250,'free_moment':569}
assert dict(thetas)=={'0':205,'1':364}
def encode(v):
 if isinstance(v,F):return str(v)
 if isinstance(v,dict):return {k:encode(x) for k,x in v.items()}
 if isinstance(v,(list,tuple)):return [encode(x) for x in v]
 return v
result={'passed':True,'scope':'Exact scalar and finite tree data controls only; no generic evaluator/coverage Lean proof; E9 unaccepted', 'margins':margins,'completion_join':joinlow,'matched_slope_case':matched,'changed_target_obstruction':obstruction,'variable_slope_mean':variable_mean,'square_crossing_zero_falsifier':True,'tree_data':{'nodes':len(nodes),'leaves':sum(counts.values()),'methods':dict(counts),'theta_counts':dict(thetas),'split_axes':dict(splits),'closed_child_geometry_checked':True},'no_proof_build':True}
(P/'result.json').write_text(json.dumps(encode(result),indent=2)+'\n')
print(json.dumps(encode(result),indent=2))
