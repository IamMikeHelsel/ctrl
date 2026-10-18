from pathlib import Path
import json,os,subprocess
HERE=Path(__file__).resolve().parent;B=HERE.parent/'builder-05'
E=json.loads((HERE/'environment.json').read_text());FRESH=Path(E['fresh_root'])
env=os.environ.copy();env.update({k:E[k] for k in ['ELAN_HOME','LEAN_PATH','PATH']})
neg=json.loads((B/'negative-clients.json').read_text())
neg.update({
'FalseRetimedReferenceBound':'''import ReviewClients
open RobotMotion RobotMotion.FutureCommit MotionReview
example : |acceleration (1/5) (realEvents (appendPending movedExecution movingBase).events) (77/100)| ≤ 1/2 := by
  rw [moved_execution_real_failure.1]
  norm_num
''',
'FalseNoDeltaTaskGoal':'''import ReviewClients
open RobotMotion RobotMotion.FutureCommit MotionReview
example : position 0 (1/5) (realEvents (appendPending noDelta movingBase).events) (17/10) = (returnTask.goal:ℝ) := by
  rw [no_delta_real_goal_failure.1]
  norm_num [returnTask]
''',
'FalseDispatchOverrunAccepted':'''import ReviewClients
open RobotMotion RobotMotion.FutureCommit MotionReview
example : commitOK pendingReturn movingBase returnTask ⟨57/100,61/100,11/1000⟩ = true := by
  rw [dispatch_overrun]
  norm_num
''',
'FalseReachableDuplicateGoal':'''import ReviewClients
open RobotMotion RobotMotion.FutureCommit MotionReview
example : position 0 (1/5) (realEvents (appendPending pendingReturn (commit pendingReturn movingBase returnTask onTime)).events) (17/10) = 0 := by
  rw [reachable_duplicate_real_failure]
  norm_num
''',
'FalseRejectionCompletesTask':'''import FutureCommitFixtures
open RobotMotion RobotMotion.FutureCommit
example : position 0 (1/5) (realEvents (commit pendingReturn movingBase returnTask tooLate).events) (17/10) = 0 := by
  rw [late_rejection_retains_old]
  norm_num [movingBase,realEvents,realEvent,position,response,F0,P]
''',
'FalseCandidateMembershipBypass':'''import ReviewClients
open RobotMotion RobotMotion.FutureCommit MotionReview
example : certificateOK missingCandidate = true := by
  rw [omitted_selected_candidate_rejected]
  norm_num
'''})
nd=HERE/'negative-clients';nd.mkdir(exist_ok=False)
results=[]
for name,text in neg.items():
    p=nd/(name+'.lean');p.write_text(text)
    r=subprocess.run([E['lean'],'--root='+str(FRESH),str(p)],cwd=FRESH,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (nd/(name+'.log')).write_text(r.stdout)
    assert r.returncode!=0 and '⊢ False' in r.stdout and 'error:' in r.stdout,(name,r.stdout)
    assert not any(x in r.stdout for x in ['unknown identifier','unknown constant','object file','unknown module prefix','application type mismatch','Application type mismatch']),(name,r.stdout)
    results.append({'name':name,'exit_code':r.returncode,'explicit_false_goal':True})
(HERE/'negative-review-result.json').write_text(json.dumps({'status':'PASS','count':len(results),'results':results},indent=2)+'\n')
