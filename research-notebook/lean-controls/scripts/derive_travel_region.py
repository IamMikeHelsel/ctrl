#!/usr/bin/env python3
"""Reproduce exact untrusted witnesses for the saturated actuator travel example.

The P below was proposed numerically, rounded to rationals, and retained only
once all four exact Bernstein/LDL witnesses existed. This script reconstructs
those witnesses; only subsequent Lean checking establishes the theorems.
"""
import json
from pathlib import Path
import sympy as s
from generate_interval_certificate import produce, ldl, mat_literal, vector
ROOT=Path(__file__).resolve().parents[1]
P=s.Matrix([[s.Rational(38,5),s.Rational(257,25),5],
 [s.Rational(257,25),s.Rational(1319,50),s.Rational(769,50)],
 [5,s.Rational(769,50),s.Rational(278,25)]])
h=s.symbols('h'); K=s.Matrix([[1,3,2]])
models=[]
for gain,gname in [(s.Rational(1,4),'Quarter'),(s.Integer(1),'Full')]:
 for exp,ename in [(1-h,'Lower'),(1-h+h*h,'Upper')]:
  F=s.Matrix([[1,h,h-1+exp],[0,1,1-exp],[0,0,exp]])
  G=s.Matrix([h*h/2-h+1-exp,h-1+exp,1-exp])
  A=(F-G*gain*K).applyfunc(s.expand)
  data={'P':[[str(v) for v in row] for row in P.tolist()],
   'A_coefficients':[[[str(s.Poly(A[i,j],h).nth(k)) for j in range(3)] for i in range(3)] for k in range(3)],
   'decay_margin':'1','partition':['0','1/5']}
  name='Travel'+gname+ename; slug='travel-'+gname.lower()+'-'+ename.lower()
  (ROOT/'benchmarks'/f'{slug}.json').write_text(json.dumps(data,indent=2)+'\n')
  source,witness=produce(data,name)
  dest=ROOT/'LeanControls/Generated'/f'{name}.lean'
  dest.write_text(source);dest.with_suffix('.certificate.json').write_text(json.dumps(witness,indent=2)+'\n')
  models.append(name)
# Conservative rational coordinate and feedback bounds, independently witnessed.
E=s.diag(1,0,0)
code=['module','public import LeanControls.Generated.TravelQuarterLower',
 '@[expose] public section','noncomputable section','namespace LeanControls.TravelGeometry',
 'open Matrix BernsteinCertificate','abbrev P := Generated.TravelQuarterLower.P']
simp='Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.vecHead, Matrix.vecTail'
for name,Q in [('positionResidual',P/3-E),('requestResidual',P/2-K.T*K)]:
 L,d=ldl(Q)
 code += [f'def {name} : Matrix (Fin 3) (Fin 3) ℝ := {mat_literal(Q)}',
  f'theorem {name}_psd : {name}.PosSemidef := by',
  f'  apply psd_of_ldl {name} {mat_literal(L)} {vector(d)}',
  '  · intro i; fin_cases i <;> norm_num',
  f'  · ext i j; fin_cases i <;> fin_cases j <;> simp [{name}, {simp}] <;> norm_num']
code+=['theorem position_energy (z : Fin 3 → ℝ) : (z 0)^2 ≤ energy P z / 3 := by',
 '  have hp := positionResidual_psd.dotProduct_mulVec_nonneg z',
 '  simp [positionResidual, energy, P, Generated.TravelQuarterLower.P, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at *',
 '  nlinarith',
 'theorem request_energy (z : Fin 3 → ℝ) : (-z 0 - 3*z 1 - 2*z 2)^2 ≤ energy P z / 2 := by',
 '  have hp := requestResidual_psd.dotProduct_mulVec_nonneg z',
 '  simp [requestResidual, energy, P, Generated.TravelQuarterLower.P, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at *',
 '  nlinarith',
 'theorem position_safe {z : Fin 3 → ℝ} (hz : energy P z ≤ 12) : |z 0| ≤ 2 := by',
 '  have hp := position_energy z',
 '  rw [abs_le]',
 '  constructor <;> nlinarith [sq_nonneg (z 0 - 2), sq_nonneg (z 0 + 2)]',
 'theorem sector_safe {z : Fin 3 → ℝ} (hz : energy P z ≤ 12) :',
 '    (1/4:ℝ) * |(-z 0 - 3*z 1 - 2*z 2)| ≤ 1 := by',
 '  have hp := request_energy z',
 '  have ha := sq_abs (-z 0 - 3*z 1 - 2*z 2)',
 '  have hn := abs_nonneg (-z 0 - 3*z 1 - 2*z 2)',
 '  nlinarith',
 'theorem active_initial_energy : energy P ![0,0,1] = 278/25 := by',
 '  norm_num [energy, P, Generated.TravelQuarterLower.P, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]',
 'end LeanControls.TravelGeometry']
(ROOT/'LeanControls/TravelGeometry.lean').write_text('\n'.join(code)+'\n')
print(json.dumps({'status':'UNVERIFIED until Lean build and axiom audit','vertices':models,
 'position_dual':str(P.inv()[0,0]),'request_dual':str((K*P.inv()*K.T)[0]),
 'disturbance_energy_endpoint_values':[str((v.T*P*v)[0]) for v in [s.Matrix([0,0,1]),s.Matrix([s.Rational(1,10),0,1]),s.Matrix([-s.Rational(1,10),s.Rational(1,5),s.Rational(4,5)])]]},indent=2))
