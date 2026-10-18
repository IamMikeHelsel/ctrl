"""Independent exact arithmetic controls; no Lean or graph endpoint proof."""
from fractions import Fraction as F
from pathlib import Path
import json

y,j,R,L=F(5,6),F(1,36),F(1,100),F(-1,15)
m,b=2*j/y,y-F(1,2)
K=4*R+1
C=j-4*R*(y-m)**2-m*m
L0=8*R*(y-m)-2*m
A=C+(L-L0)**2/(4*K)
H=((j-R)/b-L)**2/4+L*m
assert A==F(-1,5850) and H==F(-19,22500)
alpha,mu,T,Ln=1/(2*y),j/y**2,R/y**2,L/y
assert alpha==F(3,5) and mu==F(1,25)
# The graph has one unordered edge, each endpoint weight 1/5.
objective=F(1,25)*alpha**2
mass=5*alpha
cost=alpha**2/36
assert objective==F(9,625) and mass==3 and cost==R
assert y*y*objective==cost
assert 1 <= F(2,47)*36 # this cut also satisfies the structure's BCL budget
checks=[]
# Exact coefficient checks for both identities, viewed as quadratics in d.
low_coeff=[j-4*R*y*y+L*m,8*R*y-L,-K]
low_square_coeff=[A-K*(m+(L0-L)/(2*K))**2,2*K*(m+(L0-L)/(2*K)),-K]
high_coeff=[L*m,(j-R)/b-L,F(-1)]
high_square_coeff=[H-(((j-R)/b-L)/2)**2,(j-R)/b-L,F(-1)]
assert low_coeff==low_square_coeff and high_coeff==high_square_coeff
# Samples check implementation of the universal scaling identities. The report
# gives the algebraic derivation; finite checks alone are not that derivation.
for d in [F(0),F(1,6),b,m,y]:
 dl=d/y
 low=j-4*R*(y-d)**2-d*d-L*(d-m)
 lowlocal=mu-(T/alpha**2)*(1-dl)**2-dl*dl-Ln*(dl-2*mu)
 high=d*(j-R)/b-d*d-L*(d-m)
 highlocal=dl*(mu-T)/(1-alpha)-dl*dl-Ln*(dl-2*mu)
 assert low==y*y*lowlocal and high==y*y*highlocal
 checks.append({'d':str(d),'low_difference':str(low),'high_difference':str(high)})
# False alternatives must disagree on the same nonzero example.
wrong_cost=y*objective
wrong_mass=5*F(1,2)
d=F(1,6); dl=d/y
wrong_slope_difference=y*y*L*(dl-2*mu)-L*(d-m)
assert wrong_cost==F(3,250) and wrong_cost!=cost
assert wrong_mass==F(5,2) and wrong_mass!=3
assert wrong_slope_difference==F(1,900) and wrong_slope_difference!=0
assert 1/(2*F(1,2))==1 and F(1,2)-F(1,2)==0
result={
 'scope':'Exact finite controls plus coefficient checks at the disclosed example; universal algebra is reviewed in REPORT.txt, not inferred from samples.',
 'sample':{k:str(v) for k,v in dict(y=y,j=j,m=m,b=b,R=R,L=L,alpha=alpha,mu=mu,T=T,L_normalized=Ln,A=A,H=H,objective=objective,mass=mass,normalized_cost=cost).items()},
 'scaling_checks':checks,
 'rejected_alternatives':{'y_instead_of_y_squared':str(wrong_cost),'alpha_one_half_mass':str(wrong_mass),'missing_slope_scale_difference':str(wrong_slope_difference),'balanced_endpoint':'alpha=1, b=0; excluded before division'},
 'all_pass':True}
Path(__file__).with_name('result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
