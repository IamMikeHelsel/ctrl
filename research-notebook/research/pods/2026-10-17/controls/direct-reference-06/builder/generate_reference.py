#!/usr/bin/env python3
"""Encode the frozen reference coefficients exactly; no numerical fitting."""
from fractions import Fraction
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
SOURCE=HERE.parents[1]/'causal-stop-05/builder/reference.json'
def real(q):
    q=Fraction(q)
    if q.denominator==1:return str(q.numerator)
    return '('+str(q.numerator)+'/'+str(q.denominator)+')'
def render():
    phases=json.loads(SOURCE.read_text())
    lines=['module','public import Mathlib.Analysis.Calculus.Deriv.Polynomial','public import Mathlib.Tactic','@[expose] public section','noncomputable section','namespace LeanControls.DirectReference','open Polynomial','open scoped Polynomial','', '/-- Frozen phase starts, in physical seconds. -/','def phaseStart : ℕ → ℝ']
    for k,p in enumerate(phases):lines.append('  | '+str(k)+' => '+real(p['start']))
    lines+=['  | _ => 3/2','', '/-- Frozen local durations, in physical seconds. -/','def duration : ℕ → ℝ']
    for k,p in enumerate(phases):lines.append('  | '+str(k)+' => '+real(Fraction(p['end'])-Fraction(p['start'])))
    lines+=['  | _ => 0','', '/-- The eight exact local-time position polynomials used in the fixed comparison. -/','def position : ℕ → ℝ[X]']
    for k,p in enumerate(phases):
        terms=[]
        for i,c in enumerate(p['position_coefficients_local_time']):
            if Fraction(c):terms.append('C '+real(c)+(' * X' if i==1 else (' * X^'+str(i) if i else '')))
        lines.append('  | '+str(k)+' => '+' + '.join(terms))
    lines+=['  | _ => C (3/5)','', 'end LeanControls.DirectReference','']
    return '\n'.join(lines)
def main():
    output=HERE/'FrozenReference.lean'
    output.write_text(render())
    binding={'input_path':str(SOURCE),'input_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'output_sha256':hashlib.sha256(output.read_bytes()).hexdigest(),'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'coefficient_source':'exact rational values from frozen reference.json','phases':json.loads(SOURCE.read_text())}
    (HERE/'reference-binding.json').write_text(json.dumps(binding,indent=2)+'\n')
if __name__=='__main__':main()
