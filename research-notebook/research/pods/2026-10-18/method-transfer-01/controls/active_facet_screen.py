"""Exact rational preflight only. No trajectory or Lean theorem is claimed.
Check the unchanged transformed lag field on weighted-box faces. Candidate
capture radius follows the active-facet minimum mechanism from family149.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
R=F(2221,40000);W=F('0.1090800376')
weights=[F('1.02'),F('1.01'),F(1)];target=F('.045')
def rhs(r,w,z):return [4*(-z[0]+z[1]),4*(-z[1]+z[2]),4*((1-r/8)*z[0]+3*(r/8-1)*z[1]+(2-3*r/8)*z[2])+r*w/16]
def face_max(d,rho,i):
 rows=[]
 for r,w,sign in product([F(8),F(12)],[-W,W],[-1,1]):
  other=[j for j in range(3) if j!=i]
  for signs in product([-1,1],repeat=2):
   z=[F(0)]*3;z[i]=sign*d[i]*rho
   for j,s in zip(other,signs):z[j]=s*d[j]*rho
   rows.append((sign*rhs(r,w,z)[i]/d[i],r,w,z,sign))
 return max(rows,key=lambda q:q[0])
def cell(x):return {'exact':str(x),'decimal':float(x)}
rows=[]
for i in range(3):
 v,r,w,z,sign=face_max(weights,target,i)
 rows.append({'coordinate':i,'max_normalized_outward_derivative_at_target':cell(v),'maximizer':{'r':str(r),'w':str(w),'z':[str(x) for x in z],'sign':sign}})
margin=-max(F(x['max_normalized_outward_derivative_at_target']['exact']) for x in rows)
assert margin>0
slopes=[]
for i,r in product(range(3),[F(8),F(12)]):
 # Check each affine-in-radius branch separately. Subtracting two maxima
 # would not in general recover the maximum radial coefficient.
 coefficients=[]
 for sign in [-1,1]:
  other=[j for j in range(3) if j!=i]
  for signs in product([-1,1],repeat=2):
   z=[F(0)]*3;z[i]=sign*weights[i]
   for j,s in zip(other,signs):z[j]=s*weights[j]
   coefficients.append(sign*rhs(r,F(0),z)[i]/weights[i])
 worst=max(coefficients)
 assert worst<0
 slopes.append({'coordinate':i,'r':str(r),'max_radial_coefficient':cell(worst)})
time=(R-target)/margin
unweighted=[cell(face_max([F(1)]*3,target,i)[0]) for i in range(3)]
# At z=(rho,rho,rho), w=0, the first two active faces have zero derivative.
flat=rhs(F(8),F(0),[target]*3)
assert flat[0]==flat[1]==0
out={'scope':'Exact rational corner checks and algebraic candidate only; not a whole-trajectory certificate, copied-source replay, or independent acceptance.',
 'plant_source':'digital-hold-01/builder/DigitalHold.lean transformedRHS; fixed r in [8,12]',
 'residual_W':cell(W),'old_invariant_radius':cell(R),'weights':[cell(x) for x in weights],'target_weighted_radius':cell(target),
 'weighted_faces':rows,'radial_coefficients_by_rate_endpoint':slopes,'strict_margin':cell(margin),'candidate_entry_time_seconds':cell(time),
 'unweighted_face_max_at_target':unweighted,'unweighted_strict_progress_counterexample':{'z':[str(target)]*3,'r':8,'w':0,'rhs':[str(x) for x in flat]},
 'candidate_after_entry':{'position_error_m':cell(weights[0]*target),'velocity_bound_m_per_s':cell(4*(weights[0]+weights[1])*target),'acceleration_bound_m_per_s2':cell(16*(weights[0]+2*weights[1]+weights[2])*target)},
 'necessary_bridge':'Use the existing derived old-cube invariance and residual bound first. Then establish one-sided active-max comparison for every time, including held-command switches. No containment or residual may be assumed in a circular manner.'}
Path(__file__).with_name('active-facet-screen.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'margin':cell(margin),'candidate_time':cell(time),'new_position':out['candidate_after_entry']['position_error_m'],'old_position':cell(R),'flat_rhs':flat},default=str))
