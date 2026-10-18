from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
SOURCE=HERE.parent.parent/'lead-01/reference-checks.json'
STREAMS=HERE.parent.parent/'lead-01/fixed-streams.json'

def events(xs):return '['+','.join('('+x['time_s']+','+x['delta_m']+')' for x in xs)+']'
def render():
 a=json.loads(SOURCE.read_text())
 s=['import Admission','namespace RobotMotion','set_option maxRecDepth 100000','set_option maxHeartbeats 0','']
 for c in a['cases']:
  name='frozen_'+c['case']
  s += [f'def {name} : List QEvent := {events(c["accepted_events"])}',f'#eval ("{name}", check (1/5) (15/2) 0 {name})']
  # A kernel proof is kept for every final accepted history.
  s += [f'theorem {name}_checked : check (1/5) (15/2) 0 {name} = true := by decide +kernel']
  es=[]
  for i,o in enumerate(c['outcomes']):
   if o['outcome'] not in ('accepted','jerk_rejected'):continue
   proposed=es+([{'time_s':o['commit_s'],'delta_m':o['delta_m']}] if o['delta_m']!='0' else [])
   expect='true' if o['outcome']=='accepted' else 'false'
   s += [f'#eval ("{c["case"]}_admission_{i}", check (1/5) (15/2) ({o["commit_s"]}) {events(proposed)}, {expect})']
   if o['outcome']=='accepted':es=proposed
 s+=['''
theorem fixed_large_goal_rejected : check (1/5) (15/2) (11/50) [(11/50,1/20)] = false := by decide +kernel
theorem future_cancellation_accepted : check 1 1 0 [(0,1),(1/4,-1)] = true := by decide +kernel
theorem erased_commitment_rejected : check 1 1 0 [(0,1)] = false := by decide +kernel
theorem current_time_rejects : check 1 (1/4) (7/2) [(0,1)] = false := by decide +kernel
theorem old_active_rejects : check 1 1 1 [(0,1)] = false := by decide +kernel
theorem duplicate_cancellation_accepted : check 1 0 0 [(0,100),(0,-100)] = true := by decide +kernel
theorem empty_history_accepted : check 1 0 0 [] = true := by decide +kernel
theorem expired_history_accepted : check 1 0 8 [(0,1)] = true := by decide +kernel
theorem false_unit_jerk : qJerk 1 [(0,1)] 2 = -2 := by decide +kernel
theorem omit_current_passes_bad_guard :
    ((qRoots 1 [(0,1)]).filter (fun t => decide ((7/2:ℚ) ≤ t))).all
      (fun t => decide (|qJerk 1 [(0,1)] t| ≤ (1/4:ℚ))) = true := by decide +kernel
theorem omit_interior_passes_bad_guard :
    ([0,4]:List ℚ).all (fun t => decide (|qJerk 1 [(0,1)] t| ≤ 1)) = true := by decide +kernel
theorem current_witness : qJerk 1 [(0,1)] (7/2) = 1/2 := by decide +kernel

theorem half_support_position : F0 2 = (1/2:ℝ) := by norm_num [F0,P]
theorem half_support_goal_error : (1/50:ℝ) - (1/50)*F0 2 = 1/100 := by rw [half_support_position]; norm_num

def rejectedThenAccepted : List Proposal :=
  [⟨0,0,1/20⟩,⟨1/5,1/5,1/50⟩]
theorem retained_rejection_run :
    (run (1/5) (15/2) (initial 0) rejectedThenAccepted).events = [(1/5,1/50)] := by decide +kernel

def futureQueue : List Proposal := [⟨0,1,1/500⟩,⟨1/10,2,0⟩]
theorem future_queue_retained :
    (run (1/5) (15/2) (initial 0) futureQueue).events = [(1,1/500),(2,-1/500)] := by decide +kernel

end RobotMotion
''']
 return '\n'.join(s)+'\n'
if __name__=='__main__':
 (HERE/'Fixtures.lean').write_text(render())
 (HERE/'fixture-binding.json').write_text(json.dumps({'source':str(SOURCE),'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'streams_sha256':hashlib.sha256(STREAMS.read_bytes()).hexdigest(),'output_sha256':hashlib.sha256((HERE/'Fixtures.lean').read_bytes()).hexdigest()},indent=2)+'\n')
