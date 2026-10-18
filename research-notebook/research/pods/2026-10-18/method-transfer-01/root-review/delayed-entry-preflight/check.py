from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json,hashlib
weights=[F(51,50),F(101,100),F(1)];K=F(9,200);drift=F(3,1700);W=F(111,1000)
def rhs(r,w,z):
 return [4*(z[1]-z[0]),4*(z[2]-z[1]),(4-r/2)*z[0]+(-12+3*r/2)*z[1]+(8-3*r/2)*z[2]+r*w/16]
faces=[]
for i in range(3):
 for sign in [-1,1]:
  extrema=[]
  for r,w,sa,sb in product([F(8),F(12)],[-W,W],[-1,1],[-1,1]):
   z=[F(0)]*3;z[i]=sign*weights[i]*K
   rest=[v for v in range(3) if v!=i]
   z[rest[0]]=sa*weights[rest[0]]*K;z[rest[1]]=sb*weights[rest[1]]*K
   value=sign*rhs(r,w,z)[i]/weights[i]
   extrema.append((value,r,w,z))
  worst=max(extrema,key=lambda a:a[0]);assert worst[0]<=-drift
  faces.append(dict(coordinate=i,sign=sign,maximum_normalized_outward=str(worst[0]),r=str(worst[1]),w=str(worst[2]),z=list(map(str,worst[3]))))
result=dict(scope='exact algebraic face screen only; no delayed trajectory theorem',residual=str(W),target=str(K),drift=str(drift),entry_duration=str((F(2221,40000)-K)/drift),faces=faces,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path(__file__).with_name('result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
