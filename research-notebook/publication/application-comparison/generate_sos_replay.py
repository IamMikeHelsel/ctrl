#!/usr/bin/env python3
"""Translate four existing cubic Bernstein witnesses to SOS replay source.
Untrusted generator. No discovery is claimed. Run the separate Lean checker.
"""
from pathlib import Path
import hashlib,json,sys
import sympy as s
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'lean-controls/scripts'))
from generate_interval_certificate import matrix, produce, literal, poly_literal
h=s.symbols('h'); names=['TravelQuarterLower','TravelQuarterUpper','TravelFullLower','TravelFullUpper']
slugs=['travel-quarter-lower','travel-quarter-upper','travel-full-lower','travel-full-upper']
C=lambda q:f'CMvPolynomial.C ({literal(q)} : ℚ)'
X=lambda i:f'CMvPolynomial.X {i}'
code=['import SOS','open CPoly','set_option maxHeartbeats 2000000','namespace TravelSOSComparison']
records=[]
for name,slug in zip(names,slugs):
 path=ROOT/f'lean-controls/benchmarks/{slug}.json';data=json.loads(path.read_text())
 source,cert=produce(data,name);P=matrix(data['P']);As=[matrix(a) for a in data['A_coefficients']]
 A=sum((a*h**i for i,a in enumerate(As)),s.zeros(3));R=((P-A.T*P*A)/h-s.eye(3)).applyfunc(s.cancel)
 H=s.Rational(data['partition'][-1]); assert cert['degree']==3 and len(cert['segments'])==1
 vars=['x','v','a']; ep=lambda mat:' + '.join(f'({literal(mat[i,j]*(1 if i==j else 2))}) * '+(f'{vars[i]} ^ 2' if i==j else f'{vars[i]} * {vars[j]}') for i in range(3) for j in range(i,3))
 rp=' +\n    '.join(f'({poly_literal(R[i,j]*(1 if i==j else 2),h)}) * '+(f'{vars[i]} ^ 2' if i==j else f'{vars[i]} * {vars[j]}') for i in range(3) for j in range(i,3))
 coeff=cert['segments'][0]['coefficients'];sigmas=[]
 for hyp,indices in [(0,[(1,3/H,False),(3,1/H**3,True)]),(1,[(0,1/H,False),(2,3/H**3,True)])]:
  terms=[]
  for k,scale,use_h in indices:
   L=matrix(coeff[k]['L']); ds=list(map(s.Rational,coeff[k]['d']))
   factor=X(0) if use_h else f'({C(1)} - {C(1/H)} * {X(0)})'
   for j,d in enumerate(ds):
    lin=' + '.join(f'{C(L[i,j])} * {X(i+1)}' for i in range(j,3) if L[i,j]!=0)
    terms.append(f'(({literal(scale*d)} : ℚ), {factor} * ({lin}))')
  sigmas.append(f'([{hyp}], {{ terms := [\n        '+',\n        '.join(terms)+'] })')
 code += [f'namespace {name}',f'noncomputable def residual (h x v a : ℝ) : ℝ :=\n    {rp}',
 f'theorem residual_nonnegative (h x v a : ℝ) (hlo : 0 ≤ h) (hhi : h ≤ {literal(H)}) :',
 '    0 ≤ residual h x v a := by','  unfold residual','  sos_witness { sigmas := [\n    '+',\n    '.join(sigmas)+'] }',
 f'noncomputable def energy (x v a : ℝ) : ℝ := {ep(P)}']
 for i,var in enumerate(vars):
  code += [f'noncomputable def next{var.upper()} (h x v a : ℝ) : ℝ := '+' + '.join(f'({poly_literal(A[i,j],h)}) * {vars[j]}' for j in range(3))]
 code += ['theorem residual_identity (h x v a : ℝ) :',
 '    energy x v a - energy (nextX h x v a) (nextV h x v a) (nextA h x v a) -',
 '      h * (x^2 + v^2 + a^2) = h * residual h x v a := by',
 '  unfold energy nextX nextV nextA residual','  ring',
 f'theorem interval_decrease (h x v a : ℝ) (hlo : 0 ≤ h) (hhi : h ≤ {literal(H)}) :',
 '    energy (nextX h x v a) (nextV h x v a) (nextA h x v a) ≤ energy x v a - h * (x^2+v^2+a^2) := by',
 '  have hp := mul_nonneg hlo (residual_nonnegative h x v a hlo hhi)',
 '  have hi := residual_identity h x v a','  linarith',
 f'#print axioms TravelSOSComparison.{name}.residual_nonnegative',f'#print axioms TravelSOSComparison.{name}.residual_identity',f'#print axioms TravelSOSComparison.{name}.interval_decrease',f'end {name}']
 records.append({'name':name,'input':str(path.relative_to(ROOT)),'input_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'main_generated_source_sha256':hashlib.sha256(source.encode()).hexdigest(),'squares':12,'hmax':str(H),'margin':'1'})
code+=['end TravelSOSComparison']
out=Path(__file__).resolve().parent
blob=('\n'.join(code)+'\n').encode();(out/'TravelSOSReplay.lean').write_bytes(blob)
(out/'target-manifest.json').write_text(json.dumps({'status':'UNVERIFIED until separate Lean replay','generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(blob).hexdigest(),'origin':'translated existing Bernstein witnesses; no independent solver discovery','cases':records},indent=2)+'\n')
print('Generated',len(blob),'bytes; UNVERIFIED until Lean replay')
