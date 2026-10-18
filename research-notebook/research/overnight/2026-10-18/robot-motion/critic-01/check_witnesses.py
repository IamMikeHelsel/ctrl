from pathlib import Path
import datetime,hashlib,json,os,subprocess,time
HERE=Path(__file__).resolve().parent
FRESH=HERE/'.cache/fresh'
result=json.loads((HERE/'rebuild.json').read_text())
assert result['status']=='PASS'
env=os.environ.copy();env['LEAN_PATH']=result['lean_path']
lean=result['builds'][0]['command'][0]
checker=result['replays'][0]['command'][0]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(args,name,negative=False):
    t=time.monotonic()
    p=subprocess.run(args,cwd=FRESH,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    out=HERE/'logs'/(name+'.log');out.write_text(p.stdout)
    if negative:
        assert p.returncode!=0 and 'error:' in p.stdout and 'False' in p.stdout, (name,p.stdout)
        assert not any(x in p.stdout for x in ['unknown identifier','unknown constant','object file','unknown module prefix']), (name,p.stdout)
    else:assert p.returncode==0,(name,p.stdout)
    return {'exit_code':p.returncode,'seconds':time.monotonic()-t,'command':args,'log':str(out.relative_to(HERE)),'log_sha256':sha(out)}
out={'status':'RUNNING','witness_sha256':sha(HERE/'Witnesses.lean'),'negatives':[]}
(FRESH/'Witnesses.lean').write_bytes((HERE/'Witnesses.lean').read_bytes())
out['build']=run([lean,'--root='+str(FRESH),'-o',str(FRESH/'Witnesses.olean'),str(FRESH/'Witnesses.lean')],'build-Witnesses')
out['kernel']=run([checker,'Witnesses','-v'],'kernel-Witnesses')
audit=(HERE/'IndependentAudit.lean').read_text().replace('import TimedAdmission','import Witnesses').replace('`TimedAdmission]', '`TimedAdmission,`Witnesses]')
(HERE/'WitnessAudit.lean').write_text(audit)
out['audit']=run([lean,'--root='+str(FRESH),str(HERE/'WitnessAudit.lean')],'witness-audit')
out['audited_declarations']=(HERE/'logs/witness-audit.log').read_text().count('AUDIT|')
negatives={
 'FalsePlateauZero':'''example : qAcceleration 1 [(0,1),(1,2),(2,3)] (5/2) = 0 := by
  rw [plateau_nonzero]
  norm_num''',
 'FalseFutureCommitment':'''example : checkTimedCandidate 1 100 100 0 4 [(10,0)] 1 0 = true := by
  rw [future_commitment_rejected]
  norm_num''',
 'FalseExhaustiveInfeasibility':'''example : checkTimedCandidate (1/5) (1/2) (15/2) (13/25) (17/10) [(11/50,1/50)] (-1/50) (31/50) = false := by
  rw [omitted_feasible_candidate]
  norm_num''',
 'FalseTargetInferred':'''example : position 0 1 (realEvents [(0,1)]) 4 = 0 := by
  rw [accepted_target_is_sum]
  norm_num''',
 'FalseVelocityAssumed':'''example : velocity 1 (realEvents [(0,1)]) 2 ≤ 1/2 := by
  rw [admitted_reference_can_exceed_arbitrary_velocity_limit]
  norm_num''',
 'FalseCurrentTimeExcluded':'''example : checkAcceleration 1 (1/10) (7/2) [(0,1)] = true := by
  rw [current_time_rejects]
  norm_num''',
 'FalseKnotOnlySuffices':'''example : qAcceleration 1 [(0,1)] (4/3) ≤ 1/2 := by
  rw [off_knot_peak]
  norm_num''',
 'FalseOriginalAccepted':'''example : checkAcceleration (1/5) (1/2) 0 returnGenerous = true := by
  rw [new_acceleration_guard_rejects]
  norm_num''',
}
folder=HERE/'negative-controls';folder.mkdir(exist_ok=True)
for n,s in negatives.items():
    p=folder/(n+'.lean')
    p.write_text('import Witnesses\nopen RobotMotion RobotMotion.AccelerationAdmission IndependentMotionReview\n'+s+'\n')
    out['negatives'].append({'name':n,**run([lean,'--root='+str(FRESH),str(p)],'negative-'+n,True)})
out['status']='PASS';out['finished_at_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
(HERE/'witness-verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':out['status'],'negative_count':len(out['negatives']),'audited_declarations':out['audited_declarations']},indent=2))
