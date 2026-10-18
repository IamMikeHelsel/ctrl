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
audit=(HERE/'IndependentAudit.lean').read_text().replace('import PhysicalArrival','import ReviewWitnesses').replace('`PhysicalArrival]', '`PhysicalArrival,`ReviewWitnesses]')
(HERE/'WitnessAudit.lean').write_text(audit)
out['audit']=run([lean,'--root='+str(FRESH),str(HERE/'WitnessAudit.lean')],'witness-audit')
out['audited_declarations']=(HERE/'logs/witness-audit.log').read_text().count('AUDIT|')
negatives={
 'FalseExactArrival':'''example : shifted (1/80000) (17/10) 0 = 0 := by
  rw [actual_position_need_not_equal_target]
  norm_num''',
 'FalseSmallerCubeBudget':'''example : (1/100:ℝ)+(15/2)/(48*10) ≤ 2*10^2*(1/10000) := by
  norm_num''',
 'FalseRejectedGoalBecameTruth':'''example : position 0 (1/5) (realEvents [(11/50,1/50)]) (17/10) = 0 := by
  rw [retained_request_after_rejection]
  norm_num''',
 'FalseTightSelection':'''example : chooseExecution (1/5) (1/2) (15/2) (13/25) (13/10)
      [(11/50,1/50)] (-1/50) [13/25,31/50] = some (31/50) := by
  rw [tight_candidate_list_rejects]
  norm_num''',
 'FalseOriginalAcceleration':'''example : checkAcceleration (1/5) (1/2) 0 returnGenerous = true := by
  rw [new_acceleration_guard_rejects]
  norm_num''',
 'FalseReferenceAtHalfSecond':'''example : position 0 (1/5) (realEvents deferredReturn) (1/2) = 0 := by
  rw [delayed_reference_progress]
  norm_num'''}
folder=HERE/'negative-controls';folder.mkdir(exist_ok=True)
for n,s in negatives.items():
 p=folder/(n+'.lean');p.write_text('import ReviewWitnesses\nopen RobotMotion RobotMotion.AccelerationAdmission IndependentMotionReview02\n'+s+'\n')
 out['negatives'].append({'name':n,**run([lean,'--root='+str(FRESH),str(p)],'negative-'+n,True)})
out['status']='PASS';out['finished_at_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
(HERE/'witness-verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':out['status'],'negative_count':len(out['negatives']),'audited_declarations':out['audited_declarations']},indent=2))
