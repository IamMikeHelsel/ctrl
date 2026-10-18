"""Independent Fraction polynomial extrema oracle and generated Lean witnesses."""
from fractions import Fraction as Q
from math import comb, factorial
from pathlib import Path
import csv, json, random

HERE=Path(__file__).resolve().parent
B=HERE.parent/'builder-01'
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
explicit=[
 (Q(1),Q(0),[]),
 (Q(1),Q(0),[(Q(0),Q(1))]),
 (Q(1),Q(7,2),[(Q(0),Q(1))]),
 (Q(1),Q(4),[(Q(0),Q(1))]),
 (Q(1),Q(2),[(Q(0),Q(1)),(Q(1),Q(2)),(Q(2),Q(3))]),
 (Q(1),Q(1),[(Q(0),Q(1)),(Q(1),Q(3))]),
 (Q(1,2),Q(-1,3),[(Q(-2),Q(1)),(Q(0),Q(-2)),(Q(2),Q(1))]),
 (Q(1),Q(3,2),[(Q(0),Q(100)),(Q(0),Q(-100))]),
 (Q(1,5),Q(13,25),[(Q(11,50),Q(1,50)),(Q(31,50),Q(-1,50))]),
 (Q(2),Q(-4),[(Q(3),Q(-1)),(Q(-2),Q(2)),(Q(3),Q(1))]),
]
rng=random.Random(20261018)
cases=explicit+[(rng.choice([Q(1,2),Q(1),Q(2)]),Q(rng.randrange(-8,25),4),
 [(Q(rng.randrange(-4,13),3),Q(rng.randrange(-3,4),2)) for _ in range(rng.randrange(4))]) for _ in range(200)]
records=[]
for idx,(h,c,es) in enumerate(cases):
    m,op,zp,nj=oracle(h,c,es)
    ap,extras=all_pairs(h,c,es)
    am=max(abs(val(h,es,t,2)) for t in ap)
    assert m==am,(h,c,es,m,am)
    assert all(t>=c for t in ap)
    records.append({'id':idx,'h':str(h),'c':str(c),'events':[[str(t),str(d)] for t,d in es],
        'maximum':str(m),'oracle_points':len(op),'all_pair_points':len(ap),
        'outside_pair_points':len(extras),'zero_jerk_nonzero_acceleration_cells':zp,
        'constant_nonzero_jerk_cells':nj})
(HERE/'oracle-results.json').write_text(json.dumps({'seed':20261018,'status':'PASS','cases':records},indent=2)+'\n')
src=['import TimedAdmission','namespace IndependentMotionReview','open RobotMotion RobotMotion.AccelerationAdmission',
     'set_option maxRecDepth 100000','set_option maxHeartbeats 0']
for i,(h,c,es) in enumerate(explicit):
    m=oracle(h,c,es)[0]
    src.append(f'theorem oracle_boundary_{i} : checkAcceleration {leanq(h)} {leanq(m)} {leanq(c)} {leane(es)} = true := by decide +kernel')
    if m>0:
        src.append(f'theorem oracle_strict_rejection_{i} : checkAcceleration {leanq(h)} {leanq(m-Q(1,1000))} {leanq(c)} {leane(es)} = false := by decide +kernel')
src += [
 'theorem plateau_nonzero : qAcceleration 1 [(0,1),(1,2),(2,3)] (5/2) = 1 := by decide +kernel',
 'theorem plateau_zero_jerk : qJerk 1 [(0,1),(1,2),(2,3)] (5/2) = 0 := by decide +kernel',
 'theorem constant_nonzero_jerk : qJerk 1 [(0,1),(1,3)] 1 = 1 ∧ qJerk 1 [(0,1),(1,3)] 2 = 1 := by decide +kernel',
 'theorem future_commitment_rejected : checkTimedCandidate 1 100 100 0 4 [(10,0)] 1 0 = false := by decide +kernel',
 'theorem empty_candidate_list_rejected : chooseExecution (1/5) (1/2) (15/2) (13/25) (17/10) [(11/50,1/50)] (-1/50) [] = none := by rfl',
 'theorem omitted_feasible_candidate : checkTimedCandidate (1/5) (1/2) (15/2) (13/25) (17/10) [(11/50,1/50)] (-1/50) (31/50) = true := by decide +kernel',
 'theorem zero_goal_delta_is_not_inferred : checkTimedCandidate 1 100 100 0 4 [] 1 0 = true := by decide +kernel',
 'theorem accepted_target_is_sum : position 0 1 (realEvents [(0,1)]) 4 = 1 := by\n  norm_num [position,response,realEvents,realEvent,F0,P]',
 'theorem admitted_reference_can_exceed_arbitrary_velocity_limit : velocity 1 (realEvents [(0,1)]) 2 = 2/3 := by\n  norm_num [velocity,response,realEvents,realEvent,F1,P]',
 'end IndependentMotionReview']
(HERE/'Witnesses.lean').write_text('\n\n'.join(src)+'\n')
print(json.dumps({'status':'PASS','cases':len(records),'outside_pair_candidates':sum(r['outside_pair_points'] for r in records),
    'nonzero_plateau_cells':sum(r['zero_jerk_nonzero_acceleration_cells'] for r in records),
    'constant_nonzero_jerk_cells':sum(r['constant_nonzero_jerk_cells'] for r in records)},indent=2))
