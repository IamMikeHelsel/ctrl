"""Predeclared rational streams and reference-only acceptance checks.

This is a fixed mathematical screen, not a learned-policy or plant experiment.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
from knot_check import remaining_check, maximum_local_variation, reference_position

HERE=Path(__file__).resolve().parent
H=Q(1,5)
J=Q(15,2)
SERVO=Q(1,50)
TV_BUDGET=Q(3,100)

def packet(seq,observed,ready,target):
    return {"sequence": seq, "observed_s": str(Q(observed)), "ready_s": str(Q(ready)), "target_m": str(Q(target))}

def target(time,position):
    return {"time_s": str(Q(time)), "position_m": str(Q(position))}

noise=[]
for i in range(40):
    observed=Q(1,5)+Q(i,50)
    noise.append(packet(100+i,observed,observed+Q(1,50),Q((-1)**i,1000)))
noise.append(packet(140,Q(1),Q(51,50),Q(0)))
revisions=[]
for i,position in enumerate([Q(1,50),Q(41,2000),Q(39,2000),Q(41,2000),Q(39,2000),Q(1,50)]):
    observed=Q(1,5)+Q(i,20)
    revisions.append(packet(100+i,observed,observed+Q(1,50),position))

cases=[
 {"id":"hold_jitter","role":"primary","truth":[target(0,0)],"packets":noise,"deadline_s":"19/10","end_s":"5/2","task":"Actual hold error <=0.2 mm throughout; endpoint checks at deadline."},
 {"id":"persistent_goal","role":"primary","truth":[target(0,0),target(Q(1,5),Q(1,50))],"packets":[packet(100,Q(1,5),Q(11,50),Q(1,50))],"deadline_s":"3/2","end_s":"2","task":"Actual position, velocity and acceleration meet the fixed endpoint tolerances at deadline."},
 {"id":"revised_goal","role":"primary","truth":[target(0,0),target(Q(1,5),Q(1,50))],"packets":revisions,"deadline_s":"7/4","end_s":"9/4","task":"Same true 20 mm goal; noisy planner estimates do not change the external goal."},
 {"id":"late_and_stale","role":"primary","truth":[target(0,0),target(Q(1,5),Q(1,50))],"packets":[packet(20,Q(1,5),Q(8,25),Q(1,50)),packet(10,Q(1,10),Q(2,5),Q(-1,50))],"deadline_s":"3/2","end_s":"2","task":"Accept the 120 ms late new goal; discard the later-arriving older sequence."},
 {"id":"large_goal_rejection","role":"negative","truth":[target(0,0),target(Q(1,5),Q(1,20))],"packets":[packet(100,Q(1,5),Q(11,50),Q(1,20))],"deadline_s":"3/2","end_s":"2","task":"Fixed h and jerk limit reject 50 mm. Report unresolved external goal error; do not call this task success."},
 {"id":"short_deadline","role":"negative","truth":[target(0,0),target(Q(1,5),Q(1,50))],"packets":[packet(100,Q(1,5),Q(11,50),Q(1,50))],"deadline_s":"31/50","end_s":"3/2","task":"At 400 ms after acceptance, reference reaches 10 mm, not the 20 mm goal."},
 {"id":"coincident_last_write","role":"semantic","truth":[target(0,0)],"packets":[packet(100,Q(1,5),Q(11,50),Q(1,1000)),packet(101,Q(1,5),Q(11,50),Q(0))],"deadline_s":"1","end_s":"3/2","task":"Coalesce same execution time by maximum sequence before evaluating target variation."},
]

def ceil_grid(t):
    z=t/SERVO
    return Q(-(-z.numerator//z.denominator))*SERVO

def analyze(case):
    groups={}
    for item in case["packets"]:
        tau=ceil_grid(Q(item["ready_s"]))
        groups.setdefault(tau,[]).append(item)
    events=[]
    value=Q(0)
    watermark=-1
    outcomes=[]
    for tau,group in sorted(groups.items()):
        newest=max(group,key=lambda item:item["sequence"])
        for item in group:
            if item is not newest:
                outcomes.append({**item,"commit_s":str(tau),"outcome":"coalesced_by_larger_sequence"})
        if newest["sequence"] <= watermark:
            outcomes.append({**newest,"commit_s":str(tau),"outcome":"stale_discard"})
            continue
        watermark=newest["sequence"]
        candidate=Q(newest["target_m"])
        delta=candidate-value
        proposed=events+([(tau,delta)] if delta else [])
        check=remaining_check(proposed,H,J,tau)
        record={**newest,"commit_s":str(tau),"age_at_commit_s":str(tau-Q(newest["observed_s"])),"delta_m":str(delta),"future_reference_jerk_peak_m_s3":str(check["peak_abs"]),"peak_time_s":str(check["peak_time"]),"checked_future_knots":len(check["knots"])}
        if check["passed"]:
            events=proposed
            value=candidate
            record["outcome"]="accepted"
        else:
            record["outcome"]="jerk_rejected"
        outcomes.append(record)
    check=remaining_check(events,H,J,Q(0))
    variation=maximum_local_variation(events,H)
    return {"case":case["id"],"role":case["role"],"outcomes":outcomes,"accepted_events":[{"time_s":str(t),"delta_m":str(d)} for t,d in events],"final_accepted_goal_m":str(value),"exact_reference_jerk_peak_m_s3":str(check["peak_abs"]),"peak_time_s":str(check["peak_time"]),"global_knot_count":len(check["knots"]),"all_knots":[{"time_s":str(t),"jerk_m_s3":str(j)} for t,j in check["knots"]],"maximum_local_TV_m":str(variation),"TV_sufficient_gate_passes":variation<=TV_BUDGET,"reference_at_deadline_m":str(reference_position(events,H,Q(case["deadline_s"]))),"reference_tail_time_s":str(max((t for t,_ in events),default=Q(0))+4*H) if events else "0"}

spec={"version":1,"units":"SI; illustrative scalar translational axis","initial_history":"raw target zero for all t<0; filter is at rest; actual x,v,a are zero","h_s":str(H),"reference_jerk_limit_m_s3":str(J),"local_TV_sufficient_budget_m":str(TV_BUDGET),"commit_tick_s":str(SERVO),"additional_committed_buffer_s":"0","timestamp_rule":"ceil ready time to next commit tick; same-time maximum sequence wins; sequence watermark advances even if jerk admission rejects; no older packet may replace a newer observation","cases":cases}
results=[analyze(case) for case in cases]
byid={x["case"]:x for x in results}
assert all(all(x["outcome"] in ["accepted","stale_discard","coalesced_by_larger_sequence"] for x in case["outcomes"]) for case in results if case["role"]=="primary")
assert not byid["hold_jitter"]["TV_sufficient_gate_passes"]
assert Q(byid["hold_jitter"]["exact_reference_jerk_peak_m_s3"]) <= J
assert byid["large_goal_rejection"]["outcomes"][0]["outcome"] == "jerk_rejected"
assert Q(byid["short_deadline"]["reference_at_deadline_m"]) == Q(1,100)
assert byid["coincident_last_write"]["accepted_events"] == []
(HERE/"fixed-streams.json").write_text(json.dumps(spec,indent=2)+"\n")
(HERE/"reference-checks.json").write_text(json.dumps({"status":"exact rational checker outputs; continuous-time soundness still requires the proposed proof","streams_sha256":hashlib.sha256((HERE/"fixed-streams.json").read_bytes()).hexdigest(),"cases":results},indent=2)+"\n")
print(json.dumps([{k:v for k,v in r.items() if k not in ["outcomes","accepted_events","all_knots"]} for r in results],indent=2))
