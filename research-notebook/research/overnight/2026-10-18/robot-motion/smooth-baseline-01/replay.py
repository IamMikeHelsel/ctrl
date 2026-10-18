"""Build exact corrected schedules, freeze them, then replay the declared plant cases."""
from pathlib import Path
from fractions import Fraction as F
from datetime import datetime,timezone
import copy,csv,gzip,hashlib,json,sys,time
HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'builder-03'
sys.path.insert(0,str(BASE))
import run_comparison as physical
import run_experiment as scoring
from make_references import ordinary_piece
from prepare import reference_extrema
from solve import validate,sha
physical.HERE=HERE
scoring.HERE=HERE
def write(name,data):(HERE/name).write_text(json.dumps(data,indent=2)+'\n')
def now():return datetime.now(timezone.utc).isoformat()

def check_frozen():
    config=json.loads((HERE/'configuration.json').read_text())
    assert sha(BASE/'artifact-sha256.json')==config['baseline_manifest_sha256']
    for name,info in json.loads((BASE/'artifact-sha256.json').read_text())['files'].items():
        digest=info['sha256'] if isinstance(info,dict) else info
        assert sha(BASE/name)==digest,name
    for manifest in ['protocol-freeze.json','implementation-freeze.json']:
        for name,digest in json.loads((HERE/manifest).read_text())['files'].items():assert sha(HERE/name)==digest,name

def prepare():
    check_frozen();assert not (HERE/'reference-freeze.json').exists()
    originals=json.loads((BASE/'reference-schedules.json').read_text())['schedules']
    original={s['case']:s for s in originals if s['method']=='fir_checked'}
    config=json.loads((HERE/'configuration.json').read_text());schedules=[];checks=[]
    for item in json.loads((HERE/'solver-summary.json').read_text())['cases']:
        result=json.loads((HERE/(item['case']+'.json')).read_text());n=result['N'];dt=F(result['dt_s']);accepted=result['accepted']
        if accepted:
            js=list(map(F,result['corrected_jerk_nodes_SI']));initial=list(map(F,config['initial_qvaj']))
            validation,states=validate(js,dt,initial[:3],F(result['cap_m']))
            assert validation==result['validation'] and validation['passed']
            # The full rational state is propagated from the inherited reference;
            # conversion to float is only for the numerical physical integrator.
            suffix=[]
            for i,state in enumerate(states[:-1]):
                left=F(13,25)+i*dt;right=left+dt
                derivatives=[*state,js[i],(js[i+1]-js[i])/dt]
                suffix.append(ordinary_piece(left,right,derivatives,'rational_smooth_return',derivatives))
            suffix.append(ordinary_piece(F(71,50),F(5,2),[0]*5,'exact_terminal_rest',[F(0)]*5))
        cases=['return_generous','return_tight'] if n==config['N_primary'] else ['return_generous']
        for case in cases:
            schedule=copy.deepcopy(original[case]);schedule['method']='smooth_'+item['case']
            if accepted:
                prefix=[]
                for piece in original['return_generous']['pieces']:
                    left,right=map(F,[piece['start_exact'],piece['end_exact']])
                    if left>=F(13,25):break
                    clipped=copy.deepcopy(piece)
                    if right>F(13,25):clipped.update(end=.52,end_exact='13/25')
                    prefix.append(clipped)
                schedule['pieces']=prefix+suffix
                schedule['revision_execution_exact']='13/25';schedule['planned_reference_arrival_exact']='71/50'
                schedule['final_accepted_goal']=0.;schedule['revision_accepted']=True
            else:
                schedule['pieces']=copy.deepcopy(original['return_tight']['pieces'])
                schedule['revision_execution_exact']=None;schedule['planned_reference_arrival_exact']='51/50'
                schedule['final_accepted_goal']=.02;schedule['revision_accepted']=False
            schedule['reference_deadline_feasible']=F(schedule['planned_reference_arrival_exact'])<=F(schedule['deadline_exact'])
            schedule['native_duration_match']=None
            admission=schedule['admissions'][1]
            admission.update(outcome='accepted' if accepted else 'optimizer_rejected',commit_s='13/25',execution_s='13/25',actual_selected_execution_s='13/25' if accepted else None,age_at_commit_s='1/50',candidate_trials=[],decision_inputs={'solver_case':item['case'],'cap_semantics':'reference only','independent_of_task_deadline':True})
            schedule['reference_extrema']=reference_extrema(schedule['pieces'])
            schedule['optimizer_case']=item['case'];schedule['reference_cap_m']=result['cap_m'];schedule['grid_N']=n
            assert schedule['reference_extrema']['common_numerical_conformity']
            schedules.append(schedule)
        checks.append({'case':item['case'],'accepted':accepted,'solver_status':result.get('solver_status')})
    write('reference-schedules.json',{'scope':'exact corrected reference coefficients with float views for numerical propagation','schedules':schedules})
    write('reconstruction-summary.json',checks)
    names=['reference-schedules.json','reconstruction-summary.json','solver-summary.json']+[x['case']+'.json' for x in json.loads((HERE/'solver-summary.json').read_text())['cases']]
    write('reference-freeze.json',{'frozen_utc':now(),'files':{name:sha(HERE/name) for name in names}})
    print('Reference schedules frozen:',len(schedules),flush=True)

def main():
    if len(sys.argv)>1 and sys.argv[1]=='prepare':prepare();return
    check_frozen();assert not (HERE/'metrics.json').exists()
    for name,digest in json.loads((HERE/'reference-freeze.json').read_text())['files'].items():assert sha(HERE/name)==digest,name
    schedules=json.loads((HERE/'reference-schedules.json').read_text())['schedules'];summaries=[];states=[];prefixes=[];start=time.time()
    cached_baseline={}
    keys=['time_exact','side','q','qv','qa','x','v','a','reference_jerk','u','actual_jerk']
    def prefix(rows):return [{k:row[k] for k in keys} for row in rows if row['t']<F(13,25) or(row['t']==F(13,25) and row['side']=='left')]
    for step in [F(1,1000),F(1,2000)]:
        for schedule in schedules:
            if schedule['grid_N']==180 and step!=F(1,2000):continue
            for rate in [80,100,120]:
                for disturbance in [0.,.01]:
                    summary,event=physical.run_case(schedule,rate,disturbance,step)
                    extra,rows=scoring.augment(schedule,rate,disturbance,step);summary.update(extra)
                    summary.update(reference_cap_m=float(F(schedule['reference_cap_m'])),grid_N=schedule['grid_N'])
                    summaries.append(summary);states.append(event)
                    key=(rate,disturbance,str(step))
                    if key not in cached_baseline:
                        baseline=copy.deepcopy(schedule);baseline['method']='fir_checked';baseline['case']='return_generous'
                        saved=scoring.HERE;scoring.HERE=BASE
                        try:cached_baseline[key]=prefix(scoring.data_rows(baseline,rate,disturbance,step))
                        finally:scoring.HERE=saved
                    actual=prefix(rows);assert actual==cached_baseline[key],('prefix mismatch',schedule['method'],key)
                    prefixes.append({'case':schedule['case'],'method':schedule['method'],'rate':rate,'disturbance':disturbance,'step':str(step),'equal_to_accepted_baseline':True,'prefix_sha256':hashlib.sha256(json.dumps(actual,sort_keys=True).encode()).hexdigest()})
            print(schedule['case'],schedule['method'],str(step),len(summaries),flush=True)
    write('metrics.json',{'status':'root builder numerical evidence; independent review required','rows':summaries})
    write('event-states.json',states);write('common-prefix-checks.json',prefixes)
    with (HERE/'metrics.csv').open('w',newline='') as stream:
        writer=csv.DictWriter(stream,fieldnames=list(summaries[0]));writer.writeheader();writer.writerows(summaries)
    write('execution-summary.json',{'traces':len(summaries),'state_rows':sum(r['sample_count'] for r in summaries),'elapsed_s':time.time()-start,'finished_utc':now()})
    check_frozen()

if __name__=='__main__':main()
