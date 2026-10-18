#!/usr/bin/env python3
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json,random
HERE=Path(__file__).resolve().parent
y=F(5000,7797);t=F(1,2);b=y-t

def assess(n,edges,w):
 d=[sum(w[v] for a,v in edges if a==u)+sum(w[a] for a,v in edges if v==u) for u in range(n)]
 s=[sum(w[v]*d[v] for a,v in edges if a==u)+sum(w[a]*d[a] for a,v in edges if v==u) for u in range(n)]
 j=sum(w[a]*w[v] for a,v in edges)
 costs=[t*t*(j-su)/(y-du)**2 if du<=b else j-b*su/du for du,su in zip(d,s)]
 db=2*j/y
 regular=t*t*(j-db*db)/(y-db)**2 if db<=b else j-b*db
 best=min(costs)
 return j,best,regular,d,s,costs

counts={};failed=[];largest=None
for n in range(1,7):
 pairs=list(combinations(range(n),2));count=0
 for mask in range(1<<len(pairs)):
  adj=[0]*n;edges=[]
  for k,(a,v) in enumerate(pairs):
   if (mask>>k)&1:adj[a]|=1<<v;adj[v]|=1<<a;edges.append((a,v))
  if any(adj[a]&adj[v] for a,v in edges):continue
  count+=1;j,best,regular,d,s,costs=assess(n,edges,[y/n]*n)
  if best>regular:
   failed.append({'scope':'equal-weight','n':n,'edges':edges,'weights':[str(y/n)]*n,'j':str(j),'best':str(best),'regular':str(regular)})
   break
 counts[n]=count
 if failed:break
rng=random.Random(128)
hosts=[('C5',5,[(i,(i+1)%5) for i in range(5)]),('C7',7,[(i,(i+1)%7) for i in range(7)]),('Petersen',10,[(i,(i+1)%5) for i in range(5)]+[(i,i+5) for i in range(5)]+[(i+5,(i+2)%5+5) for i in range(5)])]
weighted=0
for name,n,edges in hosts:
 for k in range(1000):
  raw=[rng.randint(1,30) for _ in range(n)];w=[y*F(z,sum(raw)) for z in raw]
  j,best,regular,d,s,costs=assess(n,edges,w);weighted+=1
  if best>regular:
   failed.append({'scope':'weighted','host':name,'edges':edges,'weights':list(map(str,w)),'j':str(j),'best':str(best),'regular':str(regular),'degrees':list(map(str,d)),'neighbor_degree_sums':list(map(str,s)),'costs':list(map(str,costs))})
   break
 if len(failed)>1:break
out={'scope':'Exact falsifier of the proposed regular-profile majorant, not a graph theorem','y':str(y),'half_mass':str(t),'seed':128,'equal_weight_counts':counts,'weighted_tests':weighted,'failures':failed,'conclusion':'REJECT regular-profile majorant' if failed else 'No counterexample in the finite test; universal claim remains open'}
(HERE/'neighborhood-screen-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
