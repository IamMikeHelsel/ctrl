from pathlib import Path
import datetime,hashlib,json,os,subprocess,time
HERE=Path(__file__).resolve().parent;FRESH=HERE/'.cache/fresh'
result=json.loads((HERE/'rebuild.json').read_text())
env=os.environ.copy();env['LEAN_PATH']=result['lean_path']
lean=result['builds'][0]['command'][0];checker=str(Path(lean).parent/'leanchecker')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(args,name,negative=False):
 t=time.monotonic();p=subprocess.run(args,cwd=FRESH,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 out=HERE/'logs'/(name+'.log');out.write_text(p.stdout)
 if negative:
  assert p.returncode!=0 and 'error:' in p.stdout and 'False' in p.stdout,(name,p.stdout)
  assert not any(x in p.stdout for x in ['unknown identifier','unknown constant','object file','unknown module prefix']),(name,p.stdout)
 else:assert p.returncode==0,(name,p.stdout)
 return {'exit_code':p.returncode,'seconds':time.monotonic()-t,'command':args,'log':str(out.relative_to(HERE)),'log_sha256':sha(out)}
out={'status':'RUNNING','witness_sha256':sha(HERE/'ReviewWitnesses.lean'),'negatives':[]}
(FRESH/'ReviewWitnesses.lean').write_bytes((HERE/'ReviewWitnesses.lean').read_bytes())
out['build']=run([lean,'--root='+str(FRESH),'-o',str(FRESH/'ReviewWitnesses.olean'),str(FRESH/'ReviewWitnesses.lean')],'build-ReviewWitnesses')
out['kernel']=run([checker,'ReviewWitnesses','-v'],'kernel-ReviewWitnesses')
audit=(HERE/'IndependentAudit.lean').read_text().replace('import SuccessorGuard','import ReviewWitnesses').replace('`SuccessorGuard]', '`SuccessorGuard,`ReviewWitnesses]')
(HERE/'WitnessAudit.lean').write_text(audit)
out['audit']=run([lean,'--root='+str(FRESH),str(HERE/'WitnessAudit.lean')],'witness-audit')
out['audited_declarations']=(HERE/'logs/witness-audit.log').read_text().count('AUDIT|')
negatives={
 'FalseInteriorAccept': 'example : checkSuccessor 1 (1/2) 0 [(0,1)] = true := by\n  rw [interior_peak_rejected]\n  norm_num',
 'FalseCurrentOmitted': 'example : checkSuccessor 1 (1/10) (7/2) [(0,1)] = true := by\n  rw [current_time_rejected]\n  norm_num',
 'FalseQueuedOmitted': 'example : checkSuccessor 1 (1/2) 0 [(10,1)] = true := by\n  rw [queued_peak_rejected]\n  norm_num',
 'FalseNonStrictSuccessor': 'example : qNext [3,0,1,1,2] 1 = some 1 := by\n  rw [exact_successor]\n  norm_num',
 'FalseZeroWidthAccepted': 'example : checkSuccessor 0 1 0 [] = true := by\n  rw [zero_width_rejected]\n  norm_num',
 'FalseSignedCancellationFails': 'example : checkSuccessor 1 0 0 [(0,100),(0,-100)] = false := by\n  rw [repeated_cancel]\n  norm_num',
 'FalseAccelerationImpliesJerk': 'example : qJerk 1 [(0,1)] 1 ≤ (1/10:ℚ) := by\n  have h := acceleration_acceptance_does_not_imply_small_jerk.2\n  have hv : qJerk 1 [(0,1)] 1 = 1 := by decide +kernel\n  rw [hv]\n  norm_num'
}
folder=HERE/'negative-controls';folder.mkdir(exist_ok=True)
for n,s in negatives.items():
 p=folder/(n+'.lean');p.write_text('import ReviewWitnesses\nopen RobotMotion RobotMotion.AccelerationAdmission RobotMotion.AccelerationAdmission.SuccessorCheck IndependentSuccessorReview\n'+s+'\n')
 out['negatives'].append({'name':n,**run([lean,'--root='+str(FRESH),str(p)],'negative-'+n,True)})
out['status']='PASS';out['finished_at_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
(HERE/'witness-verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':out['status'],'negative_count':len(out['negatives']),'audited_declarations':out['audited_declarations']},indent=2))
