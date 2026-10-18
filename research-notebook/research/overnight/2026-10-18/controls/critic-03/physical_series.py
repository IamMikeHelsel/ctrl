#!/usr/bin/env python3
"""Independent scalar third-order equation, physical units, 80-digit replay.
This is a numerical series check, not an interval or tail certificate.
"""
from pathlib import Path
from fractions import Fraction
import hashlib,json,time
import mpmath as mp
HERE=Path(__file__).resolve().parent;SOURCE=HERE.parent/'builder-03'
mp.mp.dps=80
record=json.loads((SOURCE/'frozen-candidate.json').read_text())
def exact(s):
    q=Fraction(s);return mp.mpf(q.numerator)/q.denominator
t=list(map(exact,record['knots']));r=list(map(exact,record['rate']));w=list(map(exact,record['disturbance']))
T=exact(record['target_time']);z=list(map(exact,record['initial_z']))
initial=[z[0],40*(z[1]-z[0]),1600*(z[2]-2*z[1]+z[0])]

def replay(order):
    x,v,a=initial;tail=mp.mpf(0);count=0
    for j in range(len(t)-1):
        if t[j]>=T:break
        h=min(T,t[j+1])-t[j]
        r0=r[j];r1=(r[j+1]-r[j])/(t[j+1]-t[j])
        w0=w[j];w1=(w[j+1]-w[j])/(t[j+1]-t[j])
        forcing=[r0*w0,r0*w1+r1*w0,r1*w1]
        c=[x,v,a/2]
        for k in range(order-2):
            q=r0*(800*c[k]+60*(k+1)*c[k+1]+mp.mpf('1.5')*(k+2)*(k+1)*c[k+2])
            if k:
                q+=r1*(800*c[k-1]+60*k*c[k]+mp.mpf('1.5')*(k+1)*k*c[k+1])
            f=forcing[k] if k<3 else mp.mpf(0)
            c.append((f-q)/((k+3)*(k+2)*(k+1)))
        def horner(coeff):
            out=mp.mpf(0)
            for q in reversed(coeff):out=q+h*out
            return out
        x=horner(c);v=horner([k*c[k] for k in range(1,len(c))]);a=horner([k*(k-1)*c[k] for k in range(2,len(c))])
        tail=max(tail,abs(c[-1]*h**(len(c)-1)));count+=1
    return [x,v,a],tail,count

started=time.monotonic();p80,t80,n=replay(80);p110,t110,_=replay(110)
builder=json.loads((SOURCE/'high-precision-replay.json').read_text())
diff=[abs(x-exact(y)) for x,y in zip(p110,builder['physical_state'])]
orderdiff=[abs(x-y) for x,y in zip(p80,p110)]
assert max(diff)<mp.mpf('1e-55'),diff
assert max(orderdiff)<mp.mpf('1e-65'),orderdiff
result={'passed':True,'formulation':'scalar physical ODE: e3 + 1.5 r e2 + 60 r e1 + 800 r e = r w; no builder solver import','digits':80,'orders':[80,110],'target':record['target_time'],'intervals':n,'initial_physical':[mp.nstr(q,80) for q in initial],'physical_state':[mp.nstr(q,80) for q in p110],'ratio':mp.nstr(max(abs(p110[1])/mp.mpf('.001'),abs(p110[2])/mp.mpf('.02')),80),'builder_difference':[mp.nstr(q,10) for q in diff],'order_difference':[mp.nstr(q,10) for q in orderdiff],'last_position_term':[mp.nstr(t80,10),mp.nstr(t110,10)],'candidate_sha256':hashlib.sha256((SOURCE/'frozen-candidate.json').read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'seconds':time.monotonic()-started,'claim':'High-precision numerical agreement; no rigorous tail or roundoff enclosure.'}
(HERE/'physical-series.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
