"""Independent polynomial-series replay of the frozen rational candidate."""
from pathlib import Path
from fractions import Fraction
import datetime, hashlib, json, sys
import mpmath as mp
BASE=Path(__file__).resolve().parent
mp.mp.dps=60
record=json.loads((BASE/'frozen-candidate.json').read_text())
def exact(s):
    q=Fraction(s);return mp.mpf(q.numerator)/q.denominator
knots=list(map(exact,record['knots']));rates=list(map(exact,record['rate']));w=list(map(exact,record['disturbance']))
target=exact(record['target_time']);z=list(map(exact,record['initial_z']))
start=[z[0],z[1]-z[0],z[2]-2*z[1]+z[0]]

def integrate(order):
    y=start[:];max_tail=mp.mpf(0);intervals=0
    for j,(lo,hi) in enumerate(zip(knots[:-1],knots[1:])):
        if lo>=target:break
        h=min(hi,target)-lo;r0=rates[j];r1=(rates[j+1]-r0)/(hi-lo)
        w0=w[j];w1=(w[j+1]-w0)/(hi-lo)
        forcing=[r0*w0/1600,(r0*w1+r1*w0)/1600,r1*w1/1600]
        coeff=[y]
        for k in range(order):
            a=coeff[k];p=coeff[k-1] if k else [mp.mpf(0)]*3
            c=[40*a[1],40*a[2],-r0*(a[0]+3*a[1]+3*a[2])/2-r1*(p[0]+3*p[1]+3*p[2])/2]
            if k<3:c[2]+=forcing[k]
            coeff.append([v/(k+1) for v in c])
        y=[]
        for k in range(3):
            v=coeff[-1][k]
            for row in reversed(coeff[:-1]):v=row[k]+h*v
            y.append(v)
        max_tail=max(max_tail,max(abs(v*h**order) for v in coeff[-1]));intervals+=1
    return y,max_tail,intervals
y100,tail100,count=integrate(100);y120,tail120,_=integrate(120)
physical=[y120[0],40*y120[1],1600*y120[2]]
ratio=max(abs(physical[1])/mp.mpf('.001'),abs(physical[2])/mp.mpf('.02'))
result={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'candidate_sha256':hashlib.sha256((BASE/'frozen-candidate.json').read_bytes()).hexdigest(),
        'python':sys.version,'mpmath':mp.__version__,'digits':60,'orders':[100,120],
        'intervals':count,'target_time':record['target_time'],
        'initial_z':record['initial_z'],'physical_state':[mp.nstr(v,60) for v in physical],
        'normalized_ratio':mp.nstr(ratio,60),
        'order_difference_scaled':[mp.nstr(abs(a-b),8) for a,b in zip(y100,y120)],
        'largest_final_term_scaled':{'100':mp.nstr(tail100,8),'120':mp.nstr(tail120,8)},
        'claim':'High precision numerical replay. Series tail and rounding are not rigorously enclosed.'}
(BASE/'high-precision-replay.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
