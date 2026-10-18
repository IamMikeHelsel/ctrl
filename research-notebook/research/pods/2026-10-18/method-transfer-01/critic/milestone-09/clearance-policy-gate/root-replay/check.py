from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json
w=[Q('1.02'),Q('1.01'),Q(1)]
D=Q('.0005'); A=Q('1.32'); V=Q('.02')+Q('.01')+A*D; J=12*(Q('1.22')+A)
e=[Q('.001')+V*D,Q('.01')+A*D,Q('.05')+J*D]
E=[e[0],e[0]+e[1]/4,e[0]+e[1]/2+e[2]/16]
target=Q('.045');R=Q('.055525')
def policy(mx,mv,ma):
    a=[mx,mx+mv/4,mx+mv/2+ma/16]
    K=max([target]+[(a[i]-a[j]+E[i]+E[j])/(w[i]+w[j]) for i in range(3) for j in range(3)])
    lo=max(a[i]+E[i]-w[i]*K for i in range(3))
    hi=min(a[i]-E[i]+w[i]*K for i in range(3))
    assert lo<=hi
    assert all(abs(a[i]-lo)+E[i]<=w[i]*K for i in range(3))
    return dict(mx=mx,mv=mv,ma=ma,K=K,c=lo,center_hi=hi,upper=lo+w[0]*K,cube=w[0]*K)
corners=[policy(Q('.143'),v,a) for v,a in product([Q('-.01122'),Q('.01122')],[Q('-1.27'),Q('-.2')])]
assert max(x['cube'] for x in corners)<R
assert max(x['upper'] for x in corners)<Q('.15')
# K is a max of affine functions; U=max_i(a_i+E_i+(w0-wi)K)
# is convex because each w0-wi is nonnegative. Corner maxima cover rectangle.
# Translation of mx shifts U, leaves K fixed. Thus no lower mx bound needed.
slope=[-8*v-6*a-r*(Q('-1.21')+d-a)/2 for v,a,r,d in product([-V,V],[-A,A],[Q(8),Q(12)],[Q('-.01'),Q('.01')])]
assert max(map(abs,slope))<8
nom=policy(Q('.14'),Q('-.01'),Q('-1.17'))
# Equal readings/parameters for fixed weighted-radius and the variable policy.
oldc=nom['mx']+nom['mv']/4+nom['ma']/32
old_initial_K=max(target,*[(abs(x-oldc)+E[i])/w[i] for i,x in enumerate([nom['mx'],nom['mx']+nom['mv']/4,nom['mx']+nom['mv']/2+nom['ma']/16])])
negative=policy(Q('.143'),Q('.02'),Q('-1.27'))
assert negative['upper']>Q('.15')
# Nominal guard's reference-shift consequence must be disclosed.
out={'scope':'exact arithmetic preflight; no ODE or Lean acceptance','errors':e,'coordinate_errors':E,'pending_envelope':dict(A=A,V=V,J=J),'corners':corners,'maximum_K':max(x['K'] for x in corners),'maximum_upper':max(x['upper'] for x in corners),'minimum_clearance':Q('.15')-max(x['upper'] for x in corners),'nominal':nom,'fair_nominal_old_center_variable_radius':dict(c=oldc,K=old_initial_K,upper=oldc+w[0]*old_initial_K),'wider_velocity_negative':negative,'pending_slope_range':[min(slope),max(slope)],'finite_check_argument':'K is convex max of affine functions. U is max of affine plus nonnegative multiples of K, hence convex. Rectangle extrema suffice; mx translation is monotone. Pending slope is multiaffine, corner extrema suffice.'}
Path(__file__).with_name('result.json').write_text(json.dumps(out,indent=2,default=str)+'\n')
print(json.dumps({k:out[k] for k in ['maximum_K','maximum_upper','minimum_clearance','nominal','fair_nominal_old_center_variable_radius','wider_velocity_negative','pending_slope_range']},indent=2,default=str))
