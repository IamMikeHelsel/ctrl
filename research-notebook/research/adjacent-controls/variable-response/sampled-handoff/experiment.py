#!/usr/bin/env python3
"""Numerical illustration of the separately proved capture and hold contract."""
from pathlib import Path
from fractions import Fraction as F
import hashlib,importlib.util,json,math
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('brake',HERE.parent/'experiment.py')
brake=importlib.util.module_from_spec(spec);spec.loader.exec_module(brake)
READING=(F(7,50),-F(1,100),-F(117,100))
ERROR=(F(1,1000),F(1,100),F(1,20))
A=F(2);J=F(48);LIMIT=F(3,20)

def admit(delay):
    x,v,a=READING;ex,ev,ea=ERROR
    X=ex+(abs(v)+ev+A*delay)*delay;V=ev+A*delay;AA=ea+J*delay
    mid=[x,x+v/4,x+v/2+a/16];rad=[X,X+V/4,X+V/2+AA/16]
    lo=[m-e for m,e in zip(mid,rad)];hi=[m+e for m,e in zip(mid,rad)]
    low=min(lo);up=max(hi);c=(low+up)/2;R=(up-low)/2
    return dict(delay_s=str(delay),aged_error=list(map(str,(X,V,AA))),
      lower=list(map(str,lo)),upper=list(map(str,hi)),tube=[str(low),str(up)],
      center=str(c),radius=str(R),target_bound=str(26*R),
      accepted=0<=low and up<=LIMIT and 26*R<=2)

GOOD=admit(F(1,200));BAD=admit(F(1,50));C=float(F(GOOD['center']));R=float(F(GOOD['radius']))
READ_TIME=.53;DELAY=.005
at_reading=brake.held(READ_TIME-brake.DELAY,brake.engagement(.4),8.,-1.2)
at_switch=brake.held(READ_TIME+DELAY-brake.DELAY,brake.engagement(.4),8.,-1.2)

def coordinates(z):
    x,v,a=z;return(x-C,x-C+v/4,x-C+v/2+a/16)
def command(z):
    x,v,a=z;return -8*(x-C)-6*v-a/2
def solve(name,dt,horizon=5.):
    def rhs(t,z):
        if name=='release_zero':r=8.;b=0.
        else:
            r=8. if name=='hold_slow' else 10.+2.*math.sin(7.*t)
            w=0. if name=='hold_slow' else .05*math.cos(11.*t)
            b=command(z)+w
        return z[1],z[2],r*(b-z[2])
    t=0.;z=at_switch;out=[(t,*z)];maxcube=max(map(abs,coordinates(z)));maxb=0.
    n=round(horizon/dt);dt=horizon/n
    for k in range(n):
        def plus(a,b,h):return tuple(x+h*y for x,y in zip(a,b))
        k1=rhs(t,z);k2=rhs(t+dt/2,plus(z,k1,dt/2));k3=rhs(t+dt/2,plus(z,k2,dt/2));k4=rhs(t+dt,plus(z,k3,dt))
        z=tuple(x+dt*(a+2*b+2*c+d)/6 for x,a,b,c,d in zip(z,k1,k2,k3,k4));t=(k+1)*dt
        maxcube=max(maxcube,*map(abs,coordinates(z)))
        w=.05*math.cos(11*t)if name=='hold_changing' else 0.
        maxb=max(maxb,abs(command(z)+w)if name!='release_zero' else 0.)
        if (k+1)%max(1,round(.005/dt))==0:out.append((t,*z))
    return dict(name=name,samples=out,final_state=list(z),maximum_cube_coordinate=maxcube,maximum_target=maxb)

def figure(data):
    W,H=1000,480;left,top,pw,ph=85,75,850,300
    def xy(t,x):return left+pw*t/1.2,top+ph*(.16-x)/.22
    parts=[f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" role="img"><rect width="1000" height="480" fill="#fffef9"/>',
      '<style>text{font-family:system-ui,sans-serif;fill:#19372e;font-size:16px}</style>',
      '<text x="40" y="32" style="font-size:24px;font-weight:600">Zero speed does not mean safe to release.</text>']
    low,up=map(lambda x:float(F(x)),GOOD['tube']);_,yup=xy(0,up);_,ylow=xy(0,low)
    parts.append(f'<rect x="{left}" y="{yup}" width="{pw}" height="{ylow-yup}" fill="#e2efe3"/>')
    for x,label in [(0.,'0 cm'),(.05,'5 cm'),(.10,'10 cm'),(.15,'15 cm')]:
        _,y=xy(0,x);parts.extend([f'<line x1="{left}" y1="{y}" x2="{left+pw}" y2="{y}" stroke="#c7d4c9"/>',f'<text x="{left-12}" y="{y+5}" text-anchor="end">{label}</text>'])
    colors={'hold_slow':'#27744e','hold_changing':'#268f9e','release_zero':'#b74d37'}
    for row in data:
        pts=' '.join(f'{p:.2f},{q:.2f}'for t,x,*_ in row['samples']if t<=1.2 for p,q in [xy(t,x)])
        parts.append(f'<polyline points="{pts}" fill="none" stroke="{colors[row["name"]]}" stroke-width="3"/>')
    for t in [0,.3,.6,.9,1.2]:
        x,_=xy(t,0);parts.append(f'<text x="{x}" y="405" text-anchor="middle">{t:g}</text>')
    parts.append('<text x="500" y="434" text-anchor="middle">Seconds after the holding command takes effect</text>')
    for x,name,label in [(85,'hold_slow','Hold: fixed response'),(375,'hold_changing','Hold: changing response'),(700,'release_zero','Release to zero target')]:
        parts.append(f'<text x="{x}" y="469" style="fill:{colors[name]}">{label}</text>')
    parts.append('</svg>');(HERE/'comparison.svg').write_text('\n'.join(parts))

def main():
    assert GOOD['accepted'] and not BAD['accepted']
    assert all(abs(x-float(m))<=float(e)for x,m,e in zip(at_reading,READING,ERROR))
    assert max(map(abs,coordinates(at_switch)))<=R
    rows=[];refinements=[]
    for name in ['hold_slow','hold_changing','release_zero']:
        coarse=solve(name,.001);fine=solve(name,.0005)
        gap=max(abs(x-y)for x,y in zip(coarse['final_state'],fine['final_state']))
        assert gap<1e-7,(name,gap)
        if name!='release_zero':assert fine['maximum_cube_coordinate']<=R+1e-9
        rows.append(fine);refinements.append(dict(name=name,final_state_difference=gap))
    result={'scope':'Synthetic floating-point illustrations; independent Lean statements certify the conditional bounds.',
      'reading':list(map(str,READING)),'measurement_errors':list(map(str,ERROR)),
      'assumed_acceleration_bound':str(A),'assumed_jerk_bound':str(J),
      'admission':[GOOD,BAD],'reading_time_from_request':READ_TIME,'actual_state_at_reading':at_reading,
      'actual_state_at_handoff':at_switch,'examples':rows,'refinement_checks':refinements,
      'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'prior_experiment_sha256':hashlib.sha256((HERE.parent/'experiment.py').read_bytes()).hexdigest()}
    (HERE/'results.json').write_text(json.dumps(result,indent=2)+'\n');figure(rows)
    print(json.dumps({k:result[k]for k in ['admission','actual_state_at_reading','actual_state_at_handoff','refinement_checks']},indent=2))
if __name__=='__main__':main()
