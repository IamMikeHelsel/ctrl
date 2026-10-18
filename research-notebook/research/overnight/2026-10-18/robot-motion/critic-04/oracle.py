"""Reviewer oracle: cardinal B-spline recursion, not positive-part powers."""
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import json, random

HERE = Path(__file__).resolve().parent

@lru_cache(None)
def spline(n, s):
    if n == 0:
        return F(int(0 <= s < 1))
    return s/n*spline(n-1,s)+(n+1-s)/n*spline(n-1,s-1)

def jet(h, events, t):
    v = sum((d/h*spline(3,(t-tau)/h) for tau,d in events), F(0))
    a = sum((d/h**2*(spline(2,(t-tau)/h)-spline(2,(t-tau)/h-1)) for tau,d in events), F(0))
    return v,a

def coefficients(h,c,events):
    points = sorted({c}|{tau+k*h for tau,_ in events for k in range(5) if tau+k*h>=c})
    jets = {t:jet(h,events,t) for t in points}
    out = [jets[t][0] for t in points]
    identities = 0
    for left,right in zip(points,points[1:]):
        vl,al=jets[left]; vr,ar=jets[right]; d=right-left
        bs=[vl,vl+d*al/3,vr-d*ar/3,vr]
        out.extend(bs[1:3])
        for u in [F(0),F(1,7),F(1,2),F(6,7),F(1)]:
            polynomial=(1-u)**3*bs[0]+3*u*(1-u)**2*bs[1]+3*u*u*(1-u)*bs[2]+u**3*bs[3]
            assert polynomial==jet(h,events,left+u*d)[0]
            identities += 1
    assert jet(h,events,max(points)+h)==(0,0)
    return out,identities

def q(x):
    x=F(x)
    return f'({x.numerator}/{x.denominator})'

def es(xs):
    return '['+','.join(f'({q(t)},{q(d)})' for t,d in xs)+']'

def generate():
    histories=[
      (F(1),F(0),[]),
      (F(1),F(0),[(F(0),F(1)),(F(1),F(-1))]),
      (F(1),F(0),[(F(0),F(1)),(F(1,4),F(-1))]),
      (F(1),F(0),[(F(0),F(1)),(F(1,4),F(-1)),(F(1,2),F(0)),(F(3,4),F(0))]),
      (F(1),F(7,2),[(F(0),F(1))]),
      (F(1),F(4),[(F(0),F(1))]),
      (F(1),F(0),[(F(10),F(1))]),
      (F(1),F(0),[(F(10),F(-1)),(F(0),F(1))]),
      (F(1),F(0),[(F(0),F(100)),(F(0),F(-100))]),
      (F(1,5),F(13,25),[(F(11,50),F(1,50)),(F(31,50),F(-1,50))]),
      (F(2,7),F(-2),[(F(-3),F(-7,5)),(F(-2),F(3,5))]),
      (F(1,3),F(1,7),[(F(0),F(0)),(F(1,7),F(0)),(F(2),F(0))]),
      (F(1,4),F(1,4),[(F(1,4),F(1,9)),(F(1,4),F(2,9))]),
      (F(7,5),F(0),[(F(-4),F(1)),(F(4),F(-1)),(F(-4),F(-1)),(F(4),F(1))])]
    rng=random.Random(18202604)
    for _ in range(50):
        h=rng.choice([F(1,5),F(1,2),F(1),F(3,2)])
        c=F(rng.randint(-6,16),4)
        events=[(F(rng.randint(-8,20),4),F(rng.randint(-5,5),20)) for _ in range(rng.randrange(1,7))]
        if rng.randrange(3)==0: events.append(events[0])
        rng.shuffle(events); histories.append((h,c,events))
    lean=['import VelocityFixtures','open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.VelocityAdmission','set_option maxRecDepth 100000','set_option maxHeartbeats 0']
    rows=[]; identity_count=0; accepted=0; rejected=0; jetchecks=0
    for i,(h,c,events) in enumerate(histories):
        bs,count=coefficients(h,c,events); identity_count+=count
        top=max(map(abs,bs),default=F(0))
        bounds=[F(0),top,max(F(0),top-F(1,997))]
        decisions=[]
        for j,limit in enumerate(bounds):
            answer=all(abs(b)<=limit for b in bs)
            accepted+=answer; rejected+=not answer
            lean.append(f'theorem oracle_decision_{i}_{j} : checkVelocity {q(h)} {q(limit)} {q(c)} {es(events)} = {str(answer).lower()} := by decide +kernel')
            decisions.append({'limit':str(limit),'accepted':answer})
        for j,t in enumerate([c,c+h/F(7)]):
            v,a=jet(h,events,t); jetchecks+=1
            lean.append(f'theorem oracle_jet_{i}_{j} : qVelocity {q(h)} {es(events)} {q(t)} = {q(v)} ∧ qAcceleration {q(h)} {es(events)} {q(t)} = {q(a)} := by decide +kernel')
        rows.append({'h':str(h),'current':str(c),'events':[[str(t),str(d)] for t,d in events], 'max_coefficient':str(top),'decisions':decisions})
    assert max(map(abs,coefficients(F(1),F(0),[(F(0),F(1)),(F(1,4),F(-1))])[0]))==F(3,16)
    assert max(map(abs,coefficients(F(1),F(0),[(F(0),F(1)),(F(1,4),F(-1)),(F(1,2),F(0)),(F(3,4),F(0))])[0]))==F(1,6)
    assert jet(F(1),[(F(0),F(1)),(F(1),F(-1))],F(9,5))[0]==F(409,750)
    (HERE/'ReviewerOracle.lean').write_text('\n'.join(lean)+'\n')
    result={'method':'Exact cardinal B-spline degree recursion; no builder oracle imported','seed':18202604,'histories':len(histories),'decisions':accepted+rejected,'accepted':accepted,'rejected':rejected,'jet_pairs':jetchecks,'cell_identity_checks':identity_count,'cases':rows}
    (HERE/'oracle-result.json').write_text(json.dumps(result,indent=2)+'\n')
    return result

if __name__=='__main__':
    r=generate(); print(json.dumps({k:v for k,v in r.items() if k!='cases'},indent=2))
