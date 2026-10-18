"""Read-only comparison of both preserved runtime batches; no new simulation."""
from pathlib import Path
import csv,gzip,hashlib,json
HERE=Path(__file__).resolve().parent
Q=HERE/'runtime-replay-02'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    for folder,name in [(HERE,'data-sha256.json'),(Q,'data-sha256.json'),(Q,'runtime-replay-freeze.json')]:
        for n,h in json.load(open(folder/name))['files'].items():assert sha(folder/n)==h,(folder,name,n)
    a=json.load(open(HERE/'metrics.json'))['rows'];b=json.load(open(Q/'metrics.json'))['rows']
    flags=['endpoint_position_pass','endpoint_velocity_pass','endpoint_acceleration_pass','endpoint_pass','initial_response_pass','deadline_and_remain_sample_pass','causal_deadline_service_pass','all_authoritative_requests_admitted','reference_limits_numerical_pass','overall_valid_task_numerical_pass']
    key=lambda r:(r['case'],r['method'],r['rate'],r['disturbance'],r['sample_step_s'])
    amap={key(r):r for r in a};assert len(a)==len(b)==96
    changes=[]
    for row in b:
        old=amap[key(row)]
        for flag in flags:
            if row[flag]!=old[flag]:changes.append({'case':key(row),'flag':flag,'first':old[flag],'corrected':row[flag]})
    fields=['q','qv','qa','reference_jerk','reference_snap_piecewise','x','v','a','u','actual_jerk','u_derivative_piecewise','x_minus_q','x_minus_truth']
    differences={k:0. for k in fields};count=0;identical=0
    for f in sorted((HERE/'traces').glob('*.csv.gz')):
        other=Q/'traces'/f.name
        with gzip.open(f,'rt') as x,gzip.open(other,'rt') as y:
            xx=list(csv.DictReader(x));yy=list(csv.DictReader(y));assert len(xx)==len(yy)
        for x,y in zip(xx,yy):
            assert all(x[k]==y[k] for k in ['time_exact','side','labels'])
            for k in fields:differences[k]=max(differences[k],abs(float(x[k])-float(y[k])))
        count+=len(xx);identical+=sha(f)==sha(other)
    result={'passed_same_task_decisions':not changes,'scope':'Numerical runtime correction, not an independent physical replay or all-time proof','first_runtime':json.load(open(HERE/'runtime-first.json')),'canonical_runtime':json.load(open(Q/'runtime.json')),'task_decision_changes':changes,'traces':len(a),'saved_rows_compared':count,'byte_identical_trace_files':identical,'maximum_absolute_saved_row_differences':differences}
    (HERE/'runtime-comparison.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2));assert not changes
if __name__=='__main__':main()
