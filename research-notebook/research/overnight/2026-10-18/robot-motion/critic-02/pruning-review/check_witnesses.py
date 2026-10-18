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
audit=(HERE/'IndependentAudit.lean').read_text().replace('import HistoryPruning','import ReviewWitnesses').replace('`HistoryPruning]', '`HistoryPruning,`ReviewWitnesses]')
(HERE/'WitnessAudit.lean').write_text(audit)
out['audit']=run([lean,'--root='+str(FRESH),str(HERE/'WitnessAudit.lean')],'witness-audit')
out['audited_declarations']=(HERE/'logs/witness-audit.log').read_text().count('AUDIT|')
negatives={
 'FalsePastEquality': """example : position 1 1 [] 0 = position 0 1 [(0,1)] 0 := by
  rw [pruned_past_offset_one,past_motion_zero]
  norm_num""",
 'FalseActiveRemoval': """example : position 0 1 [(0,1)] 1 = 1 := by
  rw [active_motion_partial]
  norm_num""",
 'FalseQueuedRemoved': """example : qRetained 1 4 [(10,1)] = [] := by
  rw [queued_event_retained]
  norm_num""",
 'FalseUnsignedOffset': """example : qCompletedOffset 1 4 [(0,-2),(10,7),(0,3),(1,-4)] = 5 := by
  rw [exact_boundary_signed.2]
  norm_num""",
 'FalseZeroWidthPositionEquality': """example : position 0 0 [(0,1)] 0 = position 1 0 [] 0 := by
  rw [zero_width_jet_equality_fails.1,zero_width_jet_equality_fails.2]
  norm_num""",
 'FalseEndpointRetained': """example : qRetained 1 4 [(0,1)] = [(0,1)] := by
  rw [end_boundary_prunes]
  norm_num"""}
folder=HERE/'negative-controls';folder.mkdir(exist_ok=True)
for n,s in negatives.items():
 p=folder/(n+'.lean');p.write_text('import ReviewWitnesses\nopen RobotMotion RobotMotion.HistoryPruning RobotMotion.AccelerationAdmission IndependentPruningReview\n'+s+'\n')
 out['negatives'].append({'name':n,**run([lean,'--root='+str(FRESH),str(p)],'negative-'+n,True)})
out['status']='PASS';out['finished_at_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
(HERE/'witness-verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':out['status'],'negative_count':len(out['negatives']),'audited_declarations':out['audited_declarations']},indent=2))
