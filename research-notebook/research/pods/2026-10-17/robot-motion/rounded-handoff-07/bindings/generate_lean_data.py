#!/usr/bin/env python3
"""Generate exact rational Lean fixtures from frozen06 data, not printed bounds."""
from pathlib import Path
from fractions import Fraction as Q
import json,hashlib
H=Path(__file__).resolve().parent
B=H.parent.parent/'native-execution-06'/'builder'
def q(x):
 z=Q(x);return str(z.numerator) if z.denominator==1 else f'({z.numerator}/{z.denominator})'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
source=B/'reference-schedules.json'; before=sha(source)
schedules=json.loads(source.read_text())['schedules']
header='''import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

namespace NativeRational

structure Piece where
  start : ℚ
  finish : ℚ
  p : ℚ
  v : ℚ
  a : ℚ
  j : ℚ
  deriving DecidableEq, Repr

def allowance : ℚ := 1/1000000000000000
def duration (s : Piece) : ℚ := s.finish-s.start
def endP (s : Piece) : ℚ := s.p+s.v*duration s+s.a*(duration s)^2/2+s.j*(duration s)^3/6
def endV (s : Piece) : ℚ := s.v+s.a*duration s+s.j*(duration s)^2/2
def endA (s : Piece) : ℚ := s.a+s.j*duration s

def SegmentOK (s : Piece) : Prop := 0 < duration s ∧ |s.j| ≤ 15/2
instance (s : Piece) : Decidable (SegmentOK s) := inferInstanceAs (Decidable (_ ∧ _))
def JoinOK (s t : Piece) : Prop :=
  s.finish=t.start ∧
  |t.p-endP s| ≤ allowance ∧
  |(t.p-endP s)+(t.v-endV s)/40| ≤ allowance ∧
  |(t.p-endP s)+(t.v-endV s)/20+(t.a-endA s)/1600| ≤ allowance
instance (s t : Piece) : Decidable (JoinOK s t) := inferInstanceAs (Decidable (_ ∧ _))

def chainOK : List Piece → Bool
  | [] => true
  | [_] => true
  | s::t::rest => decide (JoinOK s t) && chainOK (t::rest)

def check (horizon : ℚ) (xs : List Piece) : Bool :=
  match xs with
  | [] => false
  | s::_ => decide (s.start=0 ∧ s.p=0 ∧ s.v=0 ∧ s.a=0) &&
      xs.all (fun x => decide (SegmentOK x)) && chainOK xs &&
      decide ((xs.getLast?.map Piece.finish)=some horizon)

set_option maxRecDepth 100000
set_option maxHeartbeats 0
'''
lines=[header]; records=[]
for s in schedules:
 if s['method'] not in ['ruckig','ruckig_min_08']:continue
 name=s['case']+'__'+s['method'];lines.append(f'\ndef {name} : List Piece := [')
 for k,p in enumerate(s['pieces']):
  assert Q(p['snap'])==0
  fields=[q(p['start_exact']),q(p['end_exact'])]+[q(p[n]) for n in ['p','v','a','jerk']]
  lines.append('  ⟨'+','.join(fields)+'⟩'+(',' if k+1<len(s['pieces']) else ''))
 lines.append(']')
 lines.append(f'theorem {name}_checked : check {q(s["horizon_exact"])} {name} = true := by decide +kernel')
 records.append({'name':name,'pieces':len(s['pieces']),'horizon':s['horizon_exact']})
lines.append('\nend NativeRational\n')
out=H/'NativeData.lean';out.write_text('\n'.join(lines))
assert sha(source)==before
(H/'lean-data-binding.json').write_text(json.dumps({'source_schedule_sha256':before,'generator_sha256':sha(Path(__file__)),
 'output_sha256':sha(out),'constants':'sigma10, jerk15/2, transformed allowance1/10^15; all physical conditions remain outside this checker',
 'cases':records,'source_numeric_conversion':'start/finish exact strings; coefficients exact binary Fraction(float), never rounded decimal bounds'},indent=2)+'\n')
print(len(records),'schedules',sum(x['pieces'] for x in records),'pieces',out.stat().st_size,'bytes')
