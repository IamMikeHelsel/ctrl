"""Read-only binding, causality and event continuity audit of saved data."""
from pathlib import Path
from fractions import Fraction as Q
import copy,csv,gzip,hashlib,json
import prepare
HERE=Path(__file__).resolve().parent
WORK=HERE.parents[4]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(n,x):(HERE/n).write_text(json.dumps(x,indent=2)+'\n')
def main():
    for name in ['pre-run-input-manifest.json','pre-run-implementation-manifest.json','data-sha256.json']:
        for n,h in json.loads((HERE/name).read_text())['files'].items():assert sha(HERE/n)==h,(name,n)
    spec=json.loads((HERE/'packets.json').read_text());trans=json.loads((HERE/'admission-transcripts.json').read_text())['cases']
    # Re-run only the first admission with conflicting unobserved case metadata.
    blindness=[]
    for method in spec['methods']:
        original=[]
        for case in spec['cases']:
            prefix=copy.deepcopy(case);prefix['packets']=prefix['packets'][:1]
            prefix['deadline_s']='1/1000000'
            a=prepare.schedule(prefix,method)
            prefix['deadline_s']='1000000';b=prepare.schedule(prefix,method)
            assert a==b
            assert a[2][0]['decision_inputs']['available_packet']['completion_deadline_s'] is None
            original.append(a)
        assert original[0]==original[1]
        blindness.append({'method':method,'first_admission_unchanged_by_unavailable_deadline':True})
    prior=WORK/'research/pods/2026-10-17/robot-motion/moving-goal-08/builder'
    ex=json.loads((HERE/'ruckig-primary-exports.json').read_text());old=json.loads((prior/'ruckig-primary-exports.json').read_text())
    native=[]
    for method in ['ruckig','ruckig_min_08']:
        key='return_generous__'+method
        assert ex[key]==old[key]
        native.append({'method':method,'native_plans_and_carried_inputs_exactly_equal_to08':True})
    statefields=['q','qv','qa','reference_jerk','x','v','a','u','actual_jerk']
    prefixpairs=[]
    for rate in spec['rates_per_s']:
        for w in spec['disturbances_m_s2']:
            for dt in spec['resolutions_s']:
                tables=[]
                for case in ['return_generous','return_tight']:
                    stem=f'{case}__fir_checked__r{rate}__w{int(Q(w)*100):02d}__dt{int(Q(dt)*1000000)}us'
                    with gzip.open(HERE/'traces'/(stem+'.csv.gz'),'rt') as f:rows=list(csv.DictReader(f))
                    tables.append({(r['time_exact'],r['side']):tuple(r[k] for k in statefields) for r in rows if Q(r['time_exact'])<=Q(31,50)})
                assert tables[0]==tables[1]
                prefixpairs.append({'rate':rate,'w':w,'step':dt,'through_s':'31/50','identical_rows':len(tables[0])})
    jumps=0;maxjump=0.
    for file in (HERE/'traces').glob('*__events.csv'):
        with file.open() as f:
            for row in csv.DictReader(f):
                jumps+=1;maxjump=max(maxjump,float(row['actual_state_jump_max']))
    assert maxjump==0
    selections=[]
    for tr in trans:
        if tr['method']!='fir_checked':continue
        expected=[['11/50','1/50'],['31/50','-1/50']] if tr['case']=='return_generous' else [['11/50','1/50']]
        assert tr['events']==expected
        row=tr['outcomes'][1];assert [r['candidate_s'] for r in row['candidate_trials']]==['13/25','31/50']
        assert Q(row['decision_inputs']['current_s'])>=Q(row['ready_s'])
        assert row['decision_inputs']['retained_events']==[['11/50','1/50']]
        assert row['decision_inputs']['available_packet']['completion_deadline_s'] == ('17/10' if tr['case']=='return_generous' else '13/10')
        selections.append({'case':tr['case'],'outcome':row['outcome'],'actual_selected_execution_s':row['actual_selected_execution_s'],'history':tr['events']})
    # Every negative task outcome remains in the table.
    rows=json.loads((HERE/'metrics.json').read_text())['rows'];assert len(rows)==96
    assert sum(r['method']=='fir_checked' and r['case']=='return_tight' and not r['all_authoritative_requests_admitted'] for r in rows)==12
    write('batch-audit.json',{'passed':True,'scope':'Saved-data and admission audit only; no independent physical ODE replay','input_implementation_raw_hashes_unchanged':True,'blindness':blindness,'native_prior_identity':native,'checked_prefix_pairs':prefixpairs,'selected_histories':selections,'event_rows':jumps,'maximum_physical_state_jump':maxjump,'rejected_revision_task_rows_retained':12})
    print('PASS',jumps,'event rows;',len(prefixpairs),'physical prefix pairs')
if __name__=='__main__':main()
