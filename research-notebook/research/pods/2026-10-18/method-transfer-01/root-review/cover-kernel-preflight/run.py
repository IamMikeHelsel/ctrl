#!/usr/bin/env python3
"""Bounded computation-cost test. This is not a soundness or coverage proof."""
from pathlib import Path
from fractions import Fraction
from datetime import datetime, timezone
import hashlib, json, os, subprocess, time

HERE = Path(__file__).resolve().parent
RUN = HERE.parent.parent
CERT = RUN / 'erdos/free-slope-05/certificate.json'
BIN = Path('/Users/mike/.elan/toolchains/leanprover--lean4---v4.35.0/bin')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def rat(s):
    q = Fraction(s)
    return f'({q.numerator} / {q.denominator} : Rat)'
def interval(xs): return '(' + ', '.join(map(rat, xs)) + ')'

data = json.loads(CERT.read_text())
assert sha(CERT) == '130162c84e4e7c899cf873e40cbad19bccad8d836afe86013beea700fd2e8dfb'
leaves = [(i, n) for i, n in enumerate(data['nodes']) if n['method'] == 'free_moment']
# Deterministic difficult-arithmetic sample, not a performance distribution.
leaves.sort(key=lambda p: (-max(len(s) for v in p[1]['bounds']['slopes'] for k in ['low','high'] for s in v[k]), p[0]))
selected = leaves[:16]
source = '''import Std
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace CostOnly
abbrev IV := Rat × Rat
def k (x : Rat) : IV := (x, x)
def add (a b : IV) : IV := (a.1+b.1, a.2+b.2)
def neg (a : IV) : IV := (-a.2, -a.1)
def sub (a b : IV) : IV := add a (neg b)
def mul (a b : IV) : IV :=
  (min (min (a.1*b.1) (a.1*b.2)) (min (a.2*b.1) (a.2*b.2)),
   max (max (a.1*b.1) (a.1*b.2)) (max (a.2*b.1) (a.2*b.2)))
def div (a b : IV) : IV := mul a (1/b.2, 1/b.1)
def sq (a : IV) : IV :=
  (if a.1 ≤ 0 ∧ 0 ≤ a.2 then 0 else min (a.1*a.1) (a.2*a.2),
   max (a.1*a.1) (a.2*a.2))
def R : Rat := 251/10000
def bounds (c j : IV) (t : Rat) : IV × IV :=
  let y := div (k 1) (mul (k 2) c)
  let m := mul (mul (k 4) c) j
  let b := sub y (k (1/2))
  let L0 := sub (mul (k (8*R)) (sub y m)) (mul (k 2) m)
  let C := sub (sub j (mul (k (4*R)) (sq (sub y m)))) (sq m)
  let a := div (sub j (k R)) b
  let L1 := sub a (mul (k 2) m)
  let D2 := sq (sub L1 L0)
  let Hmin := sub (mul a m) (sq m)
  (add C (div (mul (k (t*t)) D2) (k (4*(4*R+1)))),
   add Hmin (div (mul (k ((1-t)*(1-t))) D2) (k 4)))
def ok (c j : IV) (t : Rat) : Bool :=
  let v := bounds c j t
  decide (0 < c.1 ∧ c.2 < 1 ∧ c.1 ≤ c.2 ∧ j.1 ≤ j.2 ∧
    (t = 0 ∨ t = 1) ∧ v.1.2 ≤ 0 ∧ v.2.2 ≤ 0)
'''
for i, n in selected:
    source += f'theorem leaf_{i} : ok {interval(n["c"])} {interval(n["j"])} {rat(n["theta"])} = true := by decide +kernel\n'
    source += f'#print axioms leaf_{i}\n'
source += 'end CostOnly\n'
attempt = HERE / ('attempt-' + datetime.now(timezone.utc).strftime('%H%M%S'))
attempt.mkdir()
src = attempt / 'CostOnly.lean'; src.write_text(source)
env = os.environ.copy(); env['LEAN_PATH'] = str(attempt)
result = {'scope':'Closed computation cost only; no interval soundness, coverage, graph theorem, or benchmark distribution',
          'certificate_sha256':sha(CERT), 'selected_node_indices':[i for i,n in selected],
          'source_sha256':sha(src),'started_utc':datetime.now(timezone.utc).isoformat(),
          'lean_version':subprocess.check_output([str(BIN/'lean'),'--version'],text=True).strip(),
          'cap_seconds_per_command':120,'runs':[]}
def run(label, argv):
    start=time.monotonic()
    try:
        p=subprocess.run(argv,cwd=attempt,env=env,capture_output=True,text=True,timeout=120)
        code=p.returncode; out=p.stdout+p.stderr
    except subprocess.TimeoutExpired as e:
        code=124; out=str(e.stdout or '')+'\n'+str(e.stderr or '')+'\nTIMEOUT'
    (attempt/(label+'.log')).write_text(out)
    result['runs'].append({'label':label,'argv':argv,'exit':code,'seconds':time.monotonic()-start})
    (attempt/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(label,code,flush=True)
    return code
code=run('compile',[str(BIN/'lean'),'-o','CostOnly.olean','CostOnly.lean'])
if code == 0:
    code=run('kernel',[str(BIN/'leanchecker'),'CostOnly','-v'])
result['completed_utc']=datetime.now(timezone.utc).isoformat()
result['passed_computation_test']=code==0
(attempt/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
