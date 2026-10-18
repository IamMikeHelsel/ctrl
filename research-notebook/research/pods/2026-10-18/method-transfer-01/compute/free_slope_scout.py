"""Binary64 proposal screen; no universal theorem or graph counterexample."""
import datetime, hashlib, json, math, os, platform
from fractions import Fraction as F
from pathlib import Path
I=2/47
TARGETS=[.025,.0249,.0248,.0247,.0246,.0245,.0244,.0242,.024]
STOP=datetime.datetime(2026,10,18,21,45,tzinfo=datetime.timezone.utc)

def envelope(c,j):
 y=1/(2*c);x=1-y
 q=1.5*x*x-1.25*x+9/32 if x<=3/8 else x*(.5-x)/2
 return min(c*c*j, q+I-j if c>=.75 else math.inf)

def quantities(R,y,j):
 mu=2*j/y; b=y-.5; K=4*R+1
 L0=8*R*(y-mu)-2*mu; a=(j-R)/b; L1=a-2*mu
 C=j-4*R*(y-mu)**2-mu**2; Hmin=a*mu-mu**2; D2=(L1-L0)**2
 return C,Hmin,D2,K

def optimum(R,y,j):
 if y<=.5:return math.inf, None, math.inf
 C,H,D,K=quantities(R,y,j)
 def vals(t):return C+t*t*D/(4*K), H+(1-t)**2*D/4
 A0,H0=vals(0);A1,H1=vals(1)
 if A0>=H0:t=0
 elif A1<=H1:t=1
 else:
  lo=0.;hi=1.
  for _ in range(20):
   mid=(lo+hi)/2;A,B=vals(mid)
   if A<B:lo=mid
   else:hi=mid
  t=(lo+hi)/2
 A,B=vals(t)
 # Fixed small rational menu can seed an exact cover, but this evaluation is floating.
 menu=min((max(*vals(k/16)),k) for k in range(17))
 return max(A,B),t,menu[0]

rows=[dict(target=R,old_failures=0,fixed_slope_failures=0,free_slope_failures=0,menu_failures=0,first_failure=None) for R in TARGETS]
cases=0
for ci in range(801):
 if datetime.datetime.now(datetime.timezone.utc)>=STOP:raise SystemExit('Deadline')
 c=.5+.5*ci/800; y=1/(2*c)
 for ji in range(241):
  j=I*ji/240; old=envelope(c,j);cases+=1
  for row in rows:
   R=row['target']
   if old<=R:continue
   row['old_failures']+=1
   if y<=.5:best,t,menu=math.inf,None,math.inf;fixed=math.inf
   else:
    C,H,D,K=quantities(R,y,j);fixed=max(C,H+D/4)
    best,t,menu=optimum(R,y,j)
   row['fixed_slope_failures']+=fixed>0
   row['free_slope_failures']+=best>0
   row['menu_failures']+=menu>0
   if best>0 and row['first_failure'] is None:row['first_failure']=dict(c=c,j=j,y=y,old=old,minimum_majorant=best,theta=t)
# An exact local control: a menu slope must repair a known fixed-slope failure.
R=F(1,40); c=F(13,16);j=F(28,705);y=1/(2*c);mu=2*j/y;b=y-F(1,2);K=4*R+1
L0=8*R*(y-mu)-2*mu;a=(j-R)/b;L1=a-2*mu
C=j-4*R*(y-mu)**2-mu**2;H=a*mu-mu**2;D=(L1-L0)**2
assert C<0 and H+D/4>0
menu=[(max(C+F(k,16)**2*D/(4*K),H+(1-F(k,16))**2*D/4),k) for k in range(17)]
val,k=min(menu);assert val<0
for d in [F(0),b,mu,y,F(-1),F(2)]:
 L=L0+F(k,16)*(L1-L0)
 A=C+(L-L0)**2/(4*K);B=(a-L)**2/4+L*mu
 phi0=j-4*R*(y-d)**2-d*d;phi1=a*d-d*d
 assert phi0==A+L*(d-mu)-K*(d-(8*R*y-L)/(2*K))**2
 assert phi1==B+L*(d-mu)-(d-(a-L)/2)**2
result=dict(executed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),pid=os.getpid(),machine=platform.machine(),cases=cases,targets=rows,local_exact_control=dict(R=str(R),c=str(c),j=str(j),fixed_C=str(C),fixed_T=str(H+D/4),theta=str(F(k,16)),majorant=str(val)),scope='binary64 scalar screen plus one exact local Fraction control; neither universal nor graph-optimum proof',decision_rule='Propose one exact cover only. Failed sufficient inequalities are not graph counterexamples.')
print(json.dumps(result,indent=2))
