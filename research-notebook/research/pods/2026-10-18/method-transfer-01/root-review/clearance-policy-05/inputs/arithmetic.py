"""Exact rational policy certificate. No trajectory simulation or remote job."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
import hashlib,json
HERE=Path(__file__).resolve().parent
w=(F(51,50),F(101,100),F(1));target=F(9,200);R=F(2221,40000)
A=F(33,25);V=F(1533,50000);J=F(762,25);D=F(1,2000)
e=(F(1,1000)+V*D,F(1,100)+A*D,F(1,20)+J*D)
E=(e[0],e[0]+e[1]/4,e[0]+e[1]/2+e[2]/16)
def objects(m):
 x,v,a=m;z=(x,x+v/4,x+v/2+a/16)
 forms=[target]+[(z[i]-z[j]+E[i]+E[j])/(w[i]+w[j]) for i,j in product(range(3),repeat=2)]
 K=max(forms);c=max(z[i]+E[i]-w[i]*K for i in range(3));hi=min(z[i]-E[i]+w[i]*K for i in range(3))
 assert c<=hi and all(abs(z[i]-c)+E[i]<=w[i]*K for i in range(3))
 return z,forms,K,c,hi
corners=[];affine=[]
for v,a in product((-F(561,50000),F(561,50000)),(-F(127,100),-F(1,5))):
 m=(F(143,1000),v,a);z,forms,K,c,hi=objects(m)
 corners.append({'reading':list(map(str,m)),'K':str(K),'center':str(c),'center_hi':str(hi),'upper':str(c+w[0]*K)})
 for i,k in product(range(3),range(10)):
  affine.append({'v':str(v),'a':str(a),'coordinate':i,'radius_branch':k,'value':str(z[i]+E[i]+(w[0]-w[i])*forms[k])})
assert all(w[0]-wi>=0 for wi in w)
U=max(F(x['value']) for x in affine);Kmax=max(F(x['K']) for x in corners)
assert len(affine)==120 and U==F(3013722449,20100000000) and Kmax==F(2407079,50250000)
nom=(F(7,50),-F(1,100),-F(117,100));z,forms,K,c,hi=objects(nom)
cold=F(323,3200);Kold=max(target,*( (abs(z[i]-cold)+E[i])/w[i] for i in range(3)))
wide=(F(143,1000),F(1,50),-F(127,100));_,_,Kw,cw,_=objects(wide)
slopes=[-8*v-6*a-r*(-F(121,100)+d-a)/2 for v,a,r,d in product((-V,V),(-A,A),(F(8),F(12)),(-F(1,100),F(1,100)))]
assert min(slopes)==F(11967,6250) and max(slopes)==F(48533,6250)
assert K==target and c==F(9573033,100000000) and Kold==F(4948533,100000000)
assert c+w[0]*K<F(3,20)<cold+w[0]*Kold and F(3,20)<cw+w[0]*Kw
out={'scope':'Exact interval/affine algebra. Lean separately proves the continuous guard and supplied-execution dynamics. No simulation.',
 'errors':list(map(str,e)),'coordinate_errors':list(map(str,E)),'corners':corners,'affine_corner_certificate':affine,
 'finite_affine_argument':'K is max of 10 affine forms. Since w0-wi>=0, upper tube is max of 30 affine forms. Each form is affine in velocity and acceleration and has coefficient one in position; rectangle corners and mx<=.143 suffice. Lean forward_upper proves the full guard directly.',
 'maximum_K':str(Kmax),'old_cube_margin':str(R-w[0]*Kmax),'maximum_upper':str(U),'clearance_margin':str(F(3,20)-U),
 'nominal':{'K':str(K),'center':str(c),'upper':str(c+w[0]*K),'command':str(-8*(nom[0]-c)-6*nom[1]-nom[2]/2)},
 'fair_old_center':{'center':str(cold),'K':str(Kold),'upper':str(cold+w[0]*Kold)},
 'wider_speed':{'reading':list(map(str,wide)),'upper':str(cw+w[0]*Kw)},
 'pending_slope_range':list(map(str,(min(slopes),max(slopes)))),'max_entry_duration':str((Kmax-target)/F(3,1700)),
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(HERE/'arithmetic.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['maximum_K','maximum_upper','clearance_margin','nominal','fair_old_center','max_entry_duration']}))
