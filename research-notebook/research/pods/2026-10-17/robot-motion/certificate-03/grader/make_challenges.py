"""Generate independent kernel-checkable fixtures using a direct derivative oracle."""
from pathlib import Path
from fractions import Fraction as Q
from math import comb
from random import Random
import hashlib,json
HERE=Path(__file__).resolve().parent
def num(x):
 x=Q(x)
 return str(x.numerator) if x.denominator==1 else f'({x.numerator}/{x.denominator})'
def events(es):return '['+','.join(f'({num(a)},{num(d)})' for a,d in es)+']'
def jerk(h,es,t):
 return sum(d/h**3*sum(Q((-1)**i*comb(4,i))*max((t-a)/h-i,Q(0)) for i in range(5)) for a,d in es)
def peak(h,es,c):
 times={c}|{a+i*h for a,d in es for i in range(5) if a+i*h>=c}
 return max(abs(jerk(h,es,t)) for t in times)
lines=['import Composition','namespace IndependentRobotReview','open RobotMotion','set_option maxRecDepth 100000','set_option maxHeartbeats 0']
rng=Random(391744);rows=[]
for i in range(48):
 h=rng.choice([Q(1),Q(1,5),Q(1,3)])
 es=[(Q(rng.randrange(-4,13),3),Q(rng.randrange(-4,5),11)) for _ in range(i%5)]
 c=Q(rng.randrange(-4,31),7);pk=peak(h,es,c)
 for suffix,J,want in [('boundary',pk,True),('below',pk-Q(1,997),False)]:
  name=f'oracle_{i}_{suffix}'
  lines.append(f'theorem {name} : check {num(h)} {num(J)} {num(c)} {events(es)} = {str(want).lower()} := by decide +kernel')
  rows.append({'name':name,'h':str(h),'J':str(J),'c':str(c),'events':[[str(a),str(d)] for a,d in es],'oracle_peak':str(pk),'expected':want})
lines += [
'theorem invalid_width : check 0 5 0 [(0,1)] = false := by decide +kernel',
'theorem negative_width : check (-1) 5 0 [] = false := by decide +kernel',
'theorem negative_limit : check 1 (-1) 0 [] = false := by decide +kernel',
'theorem duplicate_unsorted : check 1 0 0 [(3,100),(0,20),(3,-100),(0,-20)] = true := by decide +kernel',
'theorem end_tail_exact : check 1 0 4 [(0,1)] = true := by decide +kernel',
'theorem just_before_tail_rejects : check 1 0 (399/100) [(0,1)] = false := by decide +kernel',
'theorem real_tail_interval (t : ℝ) (ht : (7/2:ℝ) ≤ t) : |jerk 1 (realEvents [(0,1)]) t| ≤ (1/2:ℝ) := by',
'  have hfuture := (check_real_iff 1 (1/2) (7/2) [(0,1)]).mp (by decide +kernel) |>.2.2 t (by norm_num; exact ht)',
'  norm_num at hfuture ⊢',
'  exact hfuture',
'def proposals : List Proposal := [⟨0,1,1/500⟩,⟨1/10,1/2,1/250⟩,⟨1/5,2,0⟩,⟨3/10,3,0⟩,⟨1/4,4,1/1000⟩,⟨2/5,4,1/20⟩]',
'theorem scheduled_events : (run (1/5) (15/2) (initial 0) proposals).events = [(1,1/500),(2,-1/500)] := by decide +kernel',
'theorem scheduled_target : (run (1/5) (15/2) (initial 0) proposals).target = 0 := by decide +kernel',
'theorem scheduled_admission_clock : (run (1/5) (15/2) (initial 0) proposals).lastAdmission = 2/5 := by decide +kernel',
'theorem scheduled_execution_clock : (run (1/5) (15/2) (initial 0) proposals).lastExecution = 2 := by decide +kernel',
'def seq0 : SequencedState := ⟨initial 0,-1⟩',
'def seq1 := submit (1/5) (15/2) seq0 50 0 ⟨0,0,1/20⟩',
'def seq2 := submit (1/5) (15/2) seq1 49 (1/10) ⟨1/5,1/5,1/1000⟩',
'def seq3 := submit (1/5) (15/2) seq2 51 (2/5) ⟨3/10,3/10,1/1000⟩',
'def seq4 := submit (1/5) (15/2) seq3 51 (2/5) ⟨2/5,2/5,1/1000⟩',
'theorem rejected_watermark : seq1.watermark = 50 ∧ seq1.motion.events = [] := by decide +kernel',
'theorem stale_after_rejection : seq2 = seq1 := by decide +kernel',
'theorem premature_after_rejection : seq3 = seq2 := by decide +kernel',
'theorem ready_recovery : seq4.watermark = 51 ∧ seq4.motion.events = [(2/5,1/1000)] := by decide +kernel',
'theorem future_prefix_at_commit : referenceJet 9 (1/5) [(1,1/500)] 0 = referenceJet 9 (1/5) [] 0 := by',
'  exact prefix_jet (by norm_num) (by norm_num : (0:ℝ) ≤ 1) 9 (1/500) [] (by norm_num)',
'end IndependentRobotReview']
(HERE/'ReviewChallenges.lean').write_text('\n'.join(lines)+'\n')
(HERE/'challenge-oracle.json').write_text(json.dumps({'fixture_count':len(rows),'oracle':'Direct third derivative of truncated-power sum with fractions; no builder or lead imports','cases':rows},indent=2)+'\n')
print(json.dumps({'oracle_fixtures':len(rows),'other_challenges':len([x for x in lines if x.startswith('theorem')])-len(rows),'sha256':hashlib.sha256((HERE/'ReviewChallenges.lean').read_bytes()).hexdigest()}))
