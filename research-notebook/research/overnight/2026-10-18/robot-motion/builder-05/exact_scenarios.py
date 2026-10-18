"""Independent Fraction evaluation of the fixed mathematical reference cases.
These scenario clocks are inputs, not measured planning durations or hardware logs.
"""
from fractions import Fraction as F
from pathlib import Path
import json
HERE=Path(__file__).resolve().parent

def jet(events,t):
    t=F(t);h=F(1,5);weights=[1,-4,6,-4,1];out=[]
    for d,denom in [(0,24),(1,6),(2,2),(3,1)]:
        val=F(0)
        for tau,delta in events:
            z=(t-F(tau))/h
            val+=F(delta)*sum(w*max(z-k,F(0))**(4-d) for k,w in enumerate(weights))/(denom*h**d)
        out.append(val)
    return out

def main():
    old=[('11/50','1/50')];combined=old+[('31/50','-1/50')]
    req=jet(old,'13/25');assert req==[F(77,19200),F(23,480),F(5,16),F(-5,4)]
    prefix={t:[str(q) for q in jet(old,t)] for t in ['13/25','57/100','31/50']}
    for t in prefix: assert jet(old,t)==jet(combined,t)
    late=jet(combined,'7/10')[0]-jet(old,'7/10')[0];assert late==F(-8,375000)
    stale=old+[('14/25','1/1000'),('31/50','-1/50')]
    assert jet(stale,'17/10')==[F(1,1000),0,0,0]
    assert jet(combined,'17/10')==[0,0,0,0]
    duplicate=combined+[('31/50','-1/50')]
    assert jet(duplicate,'17/10')==[F(-1,50),0,0,0]
    scenarios={
      'on-time':{'request':'13/25','completion':'57/100','atomic_commit':'57/100','dispatch_allowance':'1/100','execution':'31/50','reference_rest':'71/50','deadline':'17/10','decision':'accept','resulting_goal':'0'},
      'late':{'request':'13/25','completion':'7/10','atomic_commit':'7/10','dispatch_allowance':'1/100','requested_execution':'31/50','decision':'reject','fallback_final_target':'1/50','mutant_lost_contract':'unchanged prefix through commit','mutant_position_change_at_commit':str(late)},
      'stale-history':{'request':'13/25','intervening_commit':'27/50','intervening_event':['14/25','1/1000'],'completion':'57/100','atomic_commit':'57/100','execution':'31/50','decision':'reject','mutant_final_position':'1/1000','requested_goal':'0'},
      'superseded-task':{'request':'13/25','task_changed':'27/50','new_goal':'1/200','completion':'57/100','atomic_commit':'57/100','execution':'31/50','decision':'reject','mutant_final_position':'0'},
      'duplicate-result':{'request':'13/25','first_atomic_commit':'57/100','second_atomic_commit':'57/100','execution':'31/50','decision':'reject second application','mutant_final_position':'-1/50','requested_goal':'0'},
      'tight-deadline':{'request':'13/25','candidate_times':['13/25','31/50'],'deadline':'13/10','decision':'reject all supplied candidates','fallback_final_target':'1/50'}}
    data={'status':'PASS','method':'exact Python Fraction truncated-power evaluation; separate from Lean proof','clock_boundary':'declared scenario inputs, not measured computation or dispatch times','reference_only':True,'physical_simulation':False,'request_jet':dict(zip(['position_m','velocity_m_per_s','acceleration_m_per_s2','jerk_m_per_s3'],map(str,req))),'unchanged_prefix_sample_jets':prefix,'scenarios':scenarios}
    (HERE/'exact-event-log.json').write_text(json.dumps(data,indent=2)+'\n');print(json.dumps({'status':'PASS','scenarios':len(scenarios),'late_position_change_m':str(late)},indent=2))
if __name__=='__main__':main()
