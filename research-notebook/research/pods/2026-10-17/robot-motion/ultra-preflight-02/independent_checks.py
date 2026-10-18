"""Independent exact preflight checks. No plant run and no Lean proof claim.

The oracle differentiates the truncated-power sum directly. It never imports
the lead checker. Enclosures are rebuilt by exact Lagrange interpolation.
"""
from fractions import Fraction as Q
from pathlib import Path
from math import factorial, comb
import hashlib
import json
import random

HERE = Path(__file__).resolve().parent
LEAD = HERE.parent / "lead-01"
EXPECTED_MANIFEST = "9fa2ac2917bdf273c2cf4632d7da44aea08ba18a8bea8b84146eb5d2454f10ec"

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

assert digest(LEAD / "artifact-sha256.json") == EXPECTED_MANIFEST
manifest = json.loads((LEAD / "artifact-sha256.json").read_text())
before = {n: digest(LEAD / n) for n in manifest["files"]}
assert before == manifest["files"]

def kernel(z, order=0):
    assert 0 <= order <= 3
    return sum(Q((-1)**m * comb(4, m), factorial(4-order)) *
               max(z-m, Q(0))**(4-order) for m in range(5))

def ref(events, h, t, order=0):
    return sum(d * kernel((t-a)/h, order) / h**order for a, d in events)

def guard(events, h, c):
    assert h > 0
    times = sorted({c} | {a+m*h for a, _ in events for m in range(5) if a+m*h >= c})
    values = [(t, ref(events, h, t, 3)) for t in times]
    peak = max(values, key=lambda row: abs(row[1]))
    return times, values, peak

def polynomial_add(a, b):
    c = [Q(0)] * max(len(a),len(b))
    for i,v in enumerate(a): c[i] += v
    for i,v in enumerate(b): c[i] += v
    return c

def polynomial_mul(a,b):
    c = [Q(0)] * (len(a)+len(b)-1)
    for i,u in enumerate(a):
        for j,v in enumerate(b): c[i+j] += u*v
    return c

def interpolate(values):
    n = len(values)-1
    nodes = [Q(i,n) for i in range(n+1)] if n else [Q(0)]
    result = [Q(0)] * (n+1)
    for i,yi in enumerate(values):
        basis=[Q(1)]; den=Q(1)
        for j,xj in enumerate(nodes):
            if j != i:
                basis=polynomial_mul(basis,[-xj,Q(1)])
                den *= nodes[i]-xj
        result=polynomial_add(result,[yi*x/den for x in basis])
    return result

def peval(p,x):
    return sum(v*x**i for i,v in enumerate(p))

def derivative(p):
    return [i*p[i] for i in range(1,len(p))]

# Recover every F piece from five values, then differentiate algebraically.
lead_coeff = json.loads((LEAD / "kernel-coefficients.json").read_text())
piece_checks=0
for region in range(-1,5):
    if region == -1: p=[Q(0)]
    elif region == 4: p=[Q(1)]
    else:
        # Interpolation on z=region+u, then convert u=z-region.
        local=interpolate([kernel(Q(region)+Q(i,4)) for i in range(5)])
        p=[Q(0)]*5
        for i,v in enumerate(local):
            for j in range(i+1): p[j] += v*comb(i,j)*(-region)**(i-j)
        while len(p)>1 and p[-1]==0: p.pop()
    for order in range(5):
        expected=[Q(x) for x in lead_coeff["pieces"][region+1]["derivatives"][order]]
        assert p == expected, (region,order,p,expected)
        piece_checks += 1
        p=derivative(p) or [Q(0)]

spec=json.loads((LEAD / "fixed-streams.json").read_text())
recorded=json.loads((LEAD / "reference-checks.json").read_text())
h=Q(spec["h_s"]); limit=Q(spec["reference_jerk_limit_m_s3"]); tick=Q(spec["commit_tick_s"])

def schedule(packets):
    buckets={}
    for p in packets:
        r=Q(p["ready_s"])/tick
        t=Q((r.numerator+r.denominator-1)//r.denominator)*tick
        buckets.setdefault(t,[]).append(p)
    events=[]; value=Q(0); watermark=-1; out=[]
    for t, ps in sorted(buckets.items()):
        ps=sorted(ps,key=lambda p:p["sequence"])
        for p in ps[:-1]: out.append((p["sequence"],"coalesced_by_larger_sequence"))
        p=ps[-1]; seq=p["sequence"]
        if seq <= watermark:
            out.append((seq,"stale_discard")); continue
        watermark=seq
        target=Q(p["target_m"]); delta=target-value
        proposal=events+([(t,delta)] if delta else [])
        _,_,peak=guard(proposal,h,t)
        if abs(peak[1]) <= limit:
            value=target; events=proposal; out.append((seq,"accepted"))
        else: out.append((seq,"jerk_rejected"))
    return events,value,out

rows=[]
for case, saved in zip(spec["cases"],recorded["cases"]):
    assert case["id"]==saved["case"]
    events,goal,out=schedule(case["packets"])
    assert events == [(Q(e["time_s"]),Q(e["delta_m"])) for e in saved["accepted_events"]]
    assert out == [(e["sequence"],e["outcome"]) for e in saved["outcomes"]]
    times,values,peak=guard(events,h,Q(0))
    assert values == [(Q(e["time_s"]),Q(e["jerk_m_s3"])) for e in saved["all_knots"]]
    assert str(abs(peak[1]))==saved["exact_reference_jerk_peak_m_s3"]
    assert ref(events,h,Q(case["deadline_s"]))==Q(saved["reference_at_deadline_m"])
    assert goal==Q(saved["final_accepted_goal_m"])
    rows.append({"id":case["id"],"peak":str(abs(peak[1])),"events":len(events),"knots":len(times)})

# Rebuild all enclosure coefficients by values, not by the lead's expansion.
enclosures=json.loads((LEAD / "reference-enclosures.json").read_text())
enclosure_cells=0
for case, enc in zip(recorded["cases"],enclosures["cases"]):
    events=[(Q(e["time_s"]),Q(e["delta_m"])) for e in case["accepted_events"]]
    for cell in enc["cells"]:
        left=Q(cell["left_s"]); right=Q(cell["right_s"]); width=right-left
        p=interpolate([ref(events,h,left+Q(i,4)*width) for i in range(5)])
        for order in range(5):
            n=len(p)-1
            b=[sum(p[k]*Q(comb(i,k),comb(n,k)) for k in range(i+1)) for i in range(n+1)]
            assert b==[Q(v) for v in cell["bounds"][str(order)]["coefficients"]]
            if order<=3:
                assert peval(p,Q(2,7))==ref(events,h,left+Q(2,7)*width,order)
            p=[x/width for x in derivative(p)]
        enclosure_cells+=1

# Property checks include unsorted, coincident, negative, and future event times.
rng=random.Random(20261017)
histories=256; affine_checks=0
for index in range(histories):
    hh=Q(rng.randrange(1,7),rng.randrange(1,7))
    events=[(Q(rng.randrange(-8,13),4),Q(rng.randrange(-9,10),7)) for _ in range(index%8)]
    c=Q(rng.randrange(-8,37),5)
    times,values,peak=guard(events,hh,c)
    for l,r in zip(times,times[1:]):
        jl=ref(events,hh,l,3); jr=ref(events,hh,r,3)
        for theta in [Q(1,7),Q(1,2),Q(6,7)]:
            jt=ref(events,hh,l+(r-l)*theta,3)
            assert jt==(1-theta)*jl+theta*jr
            assert abs(jt)<=abs(peak[1])
            affine_checks+=1
    tail=times[-1]
    assert all(ref(events,hh,tail+gap,3)==0 for gap in [Q(0),Q(1),Q(97,3)])

# Mutations: each fails the intended theorem, with a concrete exact witness.
counterexamples={}
events=[(Q(0),Q(1))]
assert ref(events,Q(1),Q(7,2),3)==Q(1,2)
counterexamples["omit_current_time"]={"h":"1","events":[["0","1"]],"c":"7/2","J":"1/4","remaining_event_knots":["4"],"witness_jerk":"1/2"}
assert ref(events,Q(1),Q(2),3)==-2
counterexamples["omit_interior_knots"]={"h":"1","events":[["0","1"]],"checked_times":["0","4"],"J":"1","witness_time":"2","witness_jerk":"-2"}
counterexamples["drop_old_active_event"]={"h":"1","events":[["0","1"]],"c":"1","J":"1","witness_time":"2","witness_jerk":"-2"}
committed=[(Q(0),Q(1)),(Q(1,4),Q(-1))]
assert abs(guard(committed,Q(1),Q(0))[2][1])==Q(3,4)
assert abs(guard(committed[:1],Q(1),Q(0))[2][1])==2
counterexamples["erase_future_commitment"]={"h":"1","events":[["0","1"],["1/4","-1"]],"c":"0","J":"1","committed_peak":"3/4","peak_after_erase":"2"}
assert guard([(Q(0),Q(20)),(Q(0),Q(-20))],Q(1),Q(0))[2][1]==0
rejection=[{"sequence":seq,"ready_s":str(t),"target_m":str(v)} for seq,t,v in [(100,Q(1,5),Q(1,20)),(99,Q(2,5),Q(1,1000)),(101,Q(3,5),Q(1,1000))]]
assert schedule(rejection)[2]==[(100,"jerk_rejected"),(99,"stale_discard"),(101,"accepted")]

after={n:digest(LEAD/n) for n in manifest["files"]}
assert before==after
result={"status":"passed; exact finite checks only, not a Lean or Python verification theorem", "lead_manifest_sha256":EXPECTED_MANIFEST,"lead_files_preserved":len(before),"kernel_derivative_pieces":piece_checks,"cases":rows,"independent_enclosure_cells":enclosure_cells,"rational_histories":histories,"affine_interior_checks":affine_checks,"rejection_watermark":"checked","counterexamples":counterexamples}
(HERE/"independent-results.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
