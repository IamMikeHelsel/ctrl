#!/usr/bin/env python3
"""Untrusted exact-rational certificate producer; emitted Lean must be checked.

Input: rational polynomial transition A(h), rational P, a decay margin c,
and an interval partition. No expression evaluation and no floating inputs.
Output: finite Bernstein/LDL witnesses and Lean reconstruction proofs.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
from pathlib import Path
import sympy as sp


def rational(value):
    if isinstance(value, bool) or not isinstance(value, (int, str)):
        raise ValueError('Rationals must be integer or fraction strings; floats are rejected.')
    value = str(value)
    if not re.fullmatch(r'-?\d+(?:/[1-9]\d*)?', value):
        raise ValueError(f'Invalid rational: {value!r}')
    return sp.Rational(value)


def matrix(rows, n=None):
    if not isinstance(rows, list) or not rows or any(not isinstance(r, list) for r in rows):
        raise ValueError('Expected nonempty matrix rows.')
    n = n or len(rows)
    if len(rows) != n or any(len(r) != n for r in rows):
        raise ValueError('Inconsistent square matrix shape.')
    return sp.Matrix([[rational(x) for x in r] for r in rows])


def ldl(a):
    if a != a.T:
        raise ValueError('Certificate matrix is not symmetric.')
    n = a.rows
    L = sp.eye(n)
    d = []
    for j in range(n):
        pivot = a[j,j] - sum(L[j,k]**2*d[k] for k in range(j))
        if pivot < 0:
            raise ValueError(f'Negative LDL pivot at {j}: {pivot}')
        d.append(pivot)
        for i in range(j+1,n):
            residual = a[i,j] - sum(L[i,k]*L[j,k]*d[k] for k in range(j))
            if pivot == 0:
                if residual != 0:
                    raise ValueError('Zero pivot with nonzero residual; not a PSD witness.')
                L[i,j] = 0
            else:
                L[i,j] = residual/pivot
    assert L*sp.diag(*d)*L.T == a
    return L,d


def literal(q):
    q = sp.Rational(q)
    return str(q.p) if q.q == 1 else f'({q.p} / {q.q})'


def vector(v):
    return '![' + ', '.join(literal(q) for q in v) + ']'


def mat_literal(m):
    return '!![' + '; '.join(', '.join(literal(q) for q in m.row(i)) for i in range(m.rows)) + ']'


def poly_literal(p,h):
    p=sp.Poly(p,h)
    terms=[]
    for (degree,),q in p.terms():
        term=literal(q)
        if degree: term += ' * h' + (f' ^ {degree}' if degree>1 else '')
        terms.append(term)
    return ' + '.join(terms) or '0'


def poly_matrix(m,h):
    return '!![' + '; '.join(', '.join(poly_literal(m[i,j],h) for j in range(m.cols)) for i in range(m.rows)) + ']'


def produce(data, name):
    if not re.fullmatch(r'[A-Z][A-Za-z0-9_]*',name):
        raise ValueError('Namespace must be a simple uppercase Lean identifier.')
    P=matrix(data['P']);n=P.rows
    if P!=P.T: raise ValueError('P must be symmetric.')
    PL,Pd=ldl(P)
    if any(x <= 0 for x in Pd): raise ValueError('P must be positive definite, not merely symmetric.')
    lower=1/sp.trace(P.inv());upper=sp.trace(P)
    lowerL,lowerd=ldl(P-lower*sp.eye(n))
    upperL,upperd=ldl(upper*sp.eye(n)-P)
    As=[matrix(m,n) for m in data['A_coefficients']]
    if not As or As[0] != sp.eye(n): raise ValueError('A(0)=I is required for the divided residual.')
    c=rational(data['decay_margin'])
    if c<=0: raise ValueError('Decay margin must be positive.')
    cuts=[rational(t) for t in data['partition']]
    if len(cuts)<2 or cuts[0]<0 or any(a>=b for a,b in zip(cuts,cuts[1:])):
        raise ValueError('Partition must be nonnegative and strictly increasing.')
    h,t=sp.symbols('h t')
    A=sum((m*h**k for k,m in enumerate(As)),sp.zeros(n))
    residual=(P-A.T*P*A).applyfunc(lambda z:sp.cancel(z/h))-c*sp.eye(n)
    residual=residual.applyfunc(sp.expand)
    degree=max(sp.Poly(v,h).degree() for v in residual)
    degree=max(0,int(degree))
    code=['module','public import LeanControls.BernsteinCertificate','public import Mathlib.LinearAlgebra.Matrix.Notation',
          '-- Uniform generated tactics may contain unused simplification rules.', 'set_option linter.unusedSimpArgs false', 'set_option linter.unusedTactic false', 'set_option linter.unreachableTactic false', 'set_option linter.unnecessarySeqFocus false', '@[expose] public section','noncomputable section',f'namespace LeanControls.Generated.{name}',
          'open Matrix LeanControls.BernsteinCertificate',f'abbrev Mat := Matrix (Fin {n}) (Fin {n}) ℝ',
          f'def P : Mat := {mat_literal(P)}',f'def transition (h : ℝ) : Mat := {poly_matrix(A,h)}',
          f'def residual (h : ℝ) : Mat := {poly_matrix(residual,h)}']
    simp='Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail'
    evidence={'dimension':n,'degree':degree,'decay_margin':str(c),'partition':[str(x) for x in cuts],
              'verification_status':'unverified certificate witnesses; Lean checking and axiom audit required','source_sha256':hashlib.sha256(json.dumps(data,sort_keys=True).encode()).hexdigest(),'segments':[]}
    evidence['energy_lower']=str(lower);evidence['energy_upper']=str(upper)
    code += [f'def lowerBound : ℝ := {literal(lower)}',f'def upperBound : ℝ := {literal(upper)}',
             'theorem lower_pos : 0 < lowerBound := by norm_num [lowerBound]',
             'theorem upper_pos : 0 < upperBound := by norm_num [upperBound]']
    for theorem_name,expr,L,d in [('P_psd','P',PL,Pd),
        ('lower_psd','P - lowerBound • (1 : Mat)',lowerL,lowerd),
        ('upper_psd','upperBound • (1 : Mat) - P',upperL,upperd)]:
        code += [f'theorem {theorem_name} : ({expr}).PosSemidef := by',
                 f'  apply psd_of_ldl ({expr}) {mat_literal(L)} {vector(d)}',
                 '  · intro i; fin_cases i <;> norm_num',
                 f'  · ext i j; fin_cases i <;> fin_cases j <;> simp [P, lowerBound, upperBound, {simp}] <;> norm_num']
    code += [f'theorem certified_energy_bounds (x : Fin {n} → ℝ) :',
             '    lowerBound * squaredNorm x ≤ energy P x ∧ energy P x ≤ upperBound * squaredNorm x :=',
             '  energy_bounds P lower_psd upper_psd x']
    for seg,(lo,hi) in enumerate(zip(cuts,cuts[1:])):
        transformed=residual.subs(h,lo+(hi-lo)*t).applyfunc(sp.expand)
        power=[transformed.applyfunc(lambda z:sp.Poly(z,t).nth(k)) for k in range(degree+1)]
        coeff=[sum((power[k]*sp.binomial(j,k)/sp.binomial(degree,k) for k in range(j+1)),sp.zeros(n)) for j in range(degree+1)]
        reconstruction=sum((sp.binomial(degree,j)*t**j*(1-t)**(degree-j)*coeff[j] for j in range(degree+1)),sp.zeros(n))
        assert (reconstruction-transformed).applyfunc(sp.expand)==sp.zeros(n)
        segdata={'lo':str(lo),'hi':str(hi),'coefficients':[]}
        for k,C in enumerate(coeff):
            L,d=ldl(C);prefix=f's{seg}c{k}'
            code += [f'def {prefix} : Mat := {mat_literal(C)}',
                     f'theorem {prefix}_psd : {prefix}.PosSemidef := by',
                     f'  apply psd_of_ldl {prefix} {mat_literal(L)} {vector(d)}',
                     '  · intro i; fin_cases i <;> norm_num',
                     f'  · ext i j; fin_cases i <;> fin_cases j <;> simp [{prefix}, {simp}] <;> norm_num']
            segdata['coefficients'].append({'C':[[str(z) for z in row] for row in C.tolist()],
                'L':[[str(z) for z in row] for row in L.tolist()],'d':[str(z) for z in d]})
        code += [f'def coeff{seg} (k : ℕ) : Mat :=', '  match k with']
        code += [f'  | {k} => s{seg}c{k}' for k in range(degree+1)] + ['  | _ => 0']
        code += [f'theorem coeff{seg}_psd (k : ℕ) (hk : k < {degree+1}) : (coeff{seg} k).PosSemidef := by',
                 '  interval_cases k']
        code += [f'  · exact s{seg}c{k}_psd' for k in range(degree+1)]
        names=', '.join(f's{seg}c{k}' for k in range(degree+1))
        code += [f'theorem identity{seg} (t : ℝ) : residual ({literal(lo)} + ({literal(hi)} - {literal(lo)}) * t) = combination {degree} coeff{seg} t := by',
                 f'  ext i j; fin_cases i <;> fin_cases j <;> simp [residual, combination, weight, bernsteinPolynomial, Nat.choose, Finset.sum_range_succ, coeff{seg}, {names}] <;> ring',
                 f'theorem interval{seg} {{h : ℝ}} (hlo : {literal(lo)} ≤ h) (hhi : h ≤ {literal(hi)}) : (residual h).PosSemidef := by',
                 f'  exact interval_psd {degree} coeff{seg} residual (by norm_num) coeff{seg}_psd identity{seg} hlo hhi']
        evidence['segments'].append(segdata)
    code += [f'theorem residual_psd {{h : ℝ}} (hlo : {literal(cuts[0])} ≤ h) (hhi : h ≤ {literal(cuts[-1])}) : (residual h).PosSemidef := by']
    for seg in range(len(cuts)-2):
        code += [f'  by_cases hs{seg} : h ≤ {literal(cuts[seg+1])}',
                 f'  · exact interval{seg} (by linarith) hs{seg}']
    code += [f'  exact interval{len(cuts)-2} (by linarith) hhi',
             f'theorem residual_identity (h : ℝ) : P - (transition h).transpose * P * transition h - (h * {literal(c)}) • (1 : Mat) = h • residual h := by',
             f'  ext i j; fin_cases i <;> fin_cases j <;> simp [P, transition, residual, {simp}] <;> ring',
             f'theorem certified_decrease {{h : ℝ}} (hlo : {literal(cuts[0])} ≤ h) (hhi : h ≤ {literal(cuts[-1])}) (x : Fin {n} → ℝ) :',
             f'    energy P (transition h *ᵥ x) ≤ energy P x - h * {literal(c)} * squaredNorm x := by',
             '  apply step_decrease', '  rw [residual_identity]',
             '  exact (residual_psd hlo hhi).smul (by linarith)',
             f'theorem certified_contraction {{h : ℝ}} (hlo : {literal(cuts[0])} ≤ h) (hhi : h ≤ {literal(cuts[-1])}) (x : Fin {n} → ℝ) :',
             f'    energy P (transition h *ᵥ x) ≤ (1 - h * {literal(c)} / upperBound) * energy P x := by',
             '  apply contract_of_decrease P (transition h) (by linarith) (by norm_num) upper_pos upper_psd',
             '  exact certified_decrease hlo hhi',
             f'theorem certified_jitter (h : ℕ → ℝ) (x : ℕ → Fin {n} → ℝ) {{hmin : ℝ}}',
             f'    (hmin0 : {literal(cuts[0])} ≤ hmin) (hminhi : hmin ≤ {literal(cuts[-1])})',
             f'    (hlo : ∀ k, hmin ≤ h k) (hhi : ∀ k, h k ≤ {literal(cuts[-1])})',
             '    (hdyn : ∀ k, x (k+1) = transition (h k) *ᵥ x k) (n : ℕ) :',
             f'    energy P (x n) ≤ (1 - hmin * {literal(c)} / upperBound) ^ n * energy P (x 0) := by',
             '  apply jitter_energy P transition h x (by linarith) (by norm_num) upper_pos',
             '    (by dsimp [upperBound]; nlinarith) P_psd upper_psd',
             '    (fun t ht htmax => certified_decrease (by linarith) htmax) hlo hhi hdyn n',
             f'end LeanControls.Generated.{name}']
    text='\n'.join(code)+'\n'
    evidence['generated_lean_sha256']=hashlib.sha256(text.encode()).hexdigest()
    return text,evidence


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('input',type=Path);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--name',required=True);args=p.parse_args()
    data=json.loads(args.input.read_text())
    text,evidence=produce(data,args.name)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(text)
    args.output.with_suffix('.certificate.json').write_text(json.dumps(evidence,indent=2)+'\n')
    print(json.dumps({'generated':str(args.output),'status':'UNVERIFIED: run Lean','dimension':evidence['dimension'],'degree':evidence['degree']}))


if __name__=='__main__': main()
