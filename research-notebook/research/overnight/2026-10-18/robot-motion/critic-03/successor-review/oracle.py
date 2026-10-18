"""Independent Fraction polynomial extrema oracle and generated Lean witnesses."""
from fractions import Fraction as Q
from math import comb, factorial
from pathlib import Path
import csv, json, random

HERE=Path(__file__).resolve().parent
B=HERE.parent.parent/'successor-check-01'
C=(1,-4,6,-4,1)
def val(h,es,t,k):
    # k is the derivative order of position. This is a single formula,
    # independent of the builder's acceleration implementation.
    n=4-k
    return sum(d*sum(Q(c)*max(t-tau-i*h,Q(0))**n for i,c in enumerate(C)) /
               (factorial(n)*h**4) for tau,d in es)
def points(h,c,es):
    return [c]+[tau+i*h for tau,d in es for i in range(5) if tau+i*h>=c]
def all_pairs(h,c,es):
    ps=points(h,c,es)
    out=ps[:]
    extras=[]
    for l in ps:
        for r in ps:
            if l>=r:continue
            jl,jr=val(h,es,l,3),val(h,es,r,3)
            if jl==jr:continue
            z=(l*jr-r*jl)/(jr-jl)
            if z>=c:
                out.append(z)
                if z<l or z>r:extras.append((l,r,z))
    return out,extras
def oracle(h,c,es):
    # Build the quadratic acceleration polynomial on sorted cells directly.
    knots=sorted(set(points(h,c,es)))
    candidates=knots[:]
    zero_plateaus=0
    constant_nonzero_jerk=0
    for l,r in zip(knots,knots[1:]):
        mid=(l+r)/2
        a=[Q(0),Q(0),Q(0)]
        for tau,d in es:
            for i,cc in enumerate(C):
                shift=tau+i*h
                if mid<=shift:continue
                for j in range(3):
                    a[j]+=d*cc*comb(2,j)*(-shift)**(2-j)/(2*h**4)
        for t in [l,mid,r]:
            assert sum(a[j]*t**j for j in range(3))==val(h,es,t,2)
        if a[2]:
            z=-a[1]/(2*a[2])
            if l<=z<=r:candidates.append(z)
        elif a[1]:constant_nonzero_jerk+=1
        elif a[0]:zero_plateaus+=1
    return max(abs(val(h,es,t,2)) for t in candidates),candidates,zero_plateaus,constant_nonzero_jerk
def leanq(x):return f'({x.numerator}/{x.denominator} : ℚ)'
def leane(es):return '['+','.join('('+leanq(t)+','+leanq(d)+')' for t,d in es)+']'
def successor_points(h,c,es):
 ps=points(h,c,es);out=ps[:]
 for l in ps:
  later=[r for r in ps if l<r]
  if not later:continue
  r=min(later);jl=val(h,es,l,3);jr=val(h,es,r,3)
  if jl!=jr:
   z=(l*jr-r*jl)/(jr-jl)
   if l<=z<=r:out.append(z)
 return out
explicit=[(Q(1),Q(0),[]),(Q(1),Q(0),[(Q(0),Q(1))]),(Q(1),Q(7,2),[(Q(0),Q(1))]),(Q(1),Q(4),[(Q(0),Q(1))]),(Q(1),Q(2),[(Q(0),Q(1)),(Q(1),Q(2)),(Q(2),Q(3))]),(Q(1),Q(1),[(Q(0),Q(1)),(Q(1),Q(3))]),(Q(1,2),Q(-1,3),[(Q(-2),Q(1)),(Q(0),Q(-2)),(Q(2),Q(1))]),(Q(1),Q(3,2),[(Q(0),Q(100)),(Q(0),Q(-100))]),(Q(1,5),Q(13,25),[(Q(11,50),Q(1,50)),(Q(31,50),Q(-1,50))]),(Q(2),Q(-4),[(Q(3),Q(-1)),(Q(-2),Q(2)),(Q(3),Q(1))]),(Q(1),Q(0),[(Q(10),Q(1))]),(Q(1,5),Q(13,25),[(Q(11,50),Q(1,50)),(Q(13,25),Q(-1,50))])]
rng=random.Random(2026101803)
cases=explicit+[(rng.choice([Q(1,2),Q(1),Q(2)]),Q(rng.randrange(-8,25),4),[(Q(rng.randrange(-4,13),3),Q(rng.randrange(-3,4),2)) for _ in range(rng.randrange(5))]) for _ in range(200)]
records=[];decisions=[]
src=['import SuccessorGuard','namespace IndependentSuccessorReview','open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.AccelerationAdmission.SuccessorCheck','set_option maxRecDepth 100000','set_option maxHeartbeats 0']
for idx,(h,c,es) in enumerate(cases):
 peak,op,zp,nj=oracle(h,c,es);ap,extras=all_pairs(h,c,es);sp=successor_points(h,c,es)
 assert max(abs(val(h,es,t,2)) for t in ap)==max(abs(val(h,es,t,2)) for t in sp)==peak
 records.append({'id':idx,'h':str(h),'c':str(c),'events':[[str(t),str(d)] for t,d in es],'peak':str(peak),'oracle_points':len(op),'successor_points':len(sp),'all_pair_points':len(ap),'outside_pair_candidates':len(extras),'nonzero_acceleration_plateaus':zp,'constant_nonzero_jerk_cells':nj})
 for A in [peak,peak-Q(1,1000),peak+Q(1,1000)]:decisions.append((h,A,c,es,A>=peak))
 if idx<len(explicit):
  src.append(f'theorem boundary_{idx} : checkSuccessor {leanq(h)} {leanq(peak)} {leanq(c)} {leane(es)} = true := by decide +kernel')
  src.append(f'theorem below_{idx} : checkSuccessor {leanq(h)} {leanq(peak-Q(1,1000))} {leanq(c)} {leane(es)} = false := by decide +kernel')
for h in [Q(0),Q(-1)]:
 for c,es in [(Q(0),[]),(Q(1),[(Q(10),Q(1))])]:decisions.append((h,Q(100),c,es,False))
src+=['theorem exact_successor : qNext [3,0,1,1,2] 1 = some 2 := by decide +kernel','theorem fractional_current_successor : qNext [3,0,1,1,2] (3/2) = some 2 := by decide +kernel','theorem repeated_end : qNext [3,3,3] 3 = none := by decide +kernel','theorem endpoint_peak_passes_but_interior_fails : |qAcceleration 1 [(0,1)] 1| ≤ (1/2:ℚ) ∧ |qAcceleration 1 [(0,1)] 2| ≤ (1/2:ℚ) ∧ (1/2:ℚ) < |qAcceleration 1 [(0,1)] (4/3)| := by decide +kernel','theorem acceleration_acceptance_does_not_imply_small_jerk : checkSuccessor 1 (2/3) 0 [(0,1)] = true ∧ (1/10:ℚ) < qJerk 1 [(0,1)] 1 := by decide +kernel','end IndependentSuccessorReview']
(HERE/'ReviewWitnesses.lean').write_text('\n\n'.join(src)+'\n')
query=['import SuccessorGuard','open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.AccelerationAdmission.SuccessorCheck','set_option maxRecDepth 100000','set_option maxHeartbeats 0','def main : IO Unit := do']
for i,(h,A,c,es,expected) in enumerate(decisions):
 args=f'{leanq(h)} {leanq(A)} {leanq(c)} {leane(es)}'
 query.append(f'  IO.println s!"{i}|{{checkSuccessor {args}}}|{{checkAcceleration {args}}}"')
(HERE/'DecisionReplay.lean').write_text('\n'.join(query)+'\n')
(HERE/'oracle-results.json').write_text(json.dumps({'status':'PASS','seed':2026101803,'histories':records,'decisions':[{'id':i,'h':str(h),'A':str(A),'c':str(c),'events':[[str(t),str(d)] for t,d in es],'expected':ok} for i,(h,A,c,es,ok) in enumerate(decisions)]},indent=2)+'\n')
print('PASS',len(cases),'histories',len(decisions),'decisions')
