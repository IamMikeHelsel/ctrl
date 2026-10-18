#!/usr/bin/env python3
"""UNVERIFIED formal adapter data; exact symbolic checks are not Lean checks.

Translate the existing cubic Bernstein witness into the odd interval Gram
representation. Writes only this directory's UNVERIFIED-matrix-gram.json.
No generated Lean module, benchmark input, or external repository is modified.
"""
import hashlib
import json
from pathlib import Path
import sympy as s

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
INPUT = ROOT / 'lean-controls/benchmarks/double-integrator.json'
data = json.loads(INPUT.read_text())
h, t = s.symbols('h t')
matrix = lambda a: s.Matrix([[s.Rational(x) for x in row] for row in a])
P = matrix(data['P'])
A = sum((h ** k * matrix(C) for k, C in enumerate(data['A_coefficients'])), s.zeros(2))
c = s.Rational(data['decay_margin'])
assert c == 1 and data['partition'] == ['0', '1/2']
R = ((P - A.T * P * A) / h - c * s.eye(2)).applyfunc(s.cancel)
Rn = R.subs(h, t / 2).applyfunc(s.expand)
C = [s.Matrix(2, 2, lambda i, j: sum(
    Rn[i, j].coeff(t, r) * s.binomial(k, r) / s.binomial(3, r)
    for r in range(k + 1))) for k in range(4)]
assert (Rn - sum((s.binomial(3, k) * t ** k * (1-t) ** (3-k) * C[k]
                  for k in range(4)), s.zeros(2))).applyfunc(s.expand) == s.zeros(2)
Gleft = (3*C[1]).row_join(-3*C[1]).col_join((-3*C[1]).row_join(3*C[1]+C[3]))
Gright = C[0].row_join(-C[0]).col_join((-C[0]).row_join(C[0]+3*C[2]))
Z = s.eye(2).col_join(t*s.eye(2))
assert (Rn - t*Z.T*Gleft*Z - (1-t)*Z.T*Gright*Z).applyfunc(s.expand) == s.zeros(2)

def rows(M):
    return [[str(M[i, j]) for j in range(M.cols)] for i in range(M.rows)]

def gram_record(G):
    L, D = G.LDLdecomposition(hermitian=False)
    assert L*D*L.T == G and all(d > 0 for d in D.diagonal())
    return {'matrix': rows(G), 'L': rows(L), 'D_diagonal': [str(x) for x in D.diagonal()]}

result = {
    'status': 'UNVERIFIED: exact SymPy identities checked; no MatrixSOS Lean adapter built',
    'input': 'lean-controls/benchmarks/double-integrator.json',
    'input_sha256': hashlib.sha256(INPUT.read_bytes()).hexdigest(),
    'sympy_version': s.__version__,
    'A_h': rows(A), 'P': rows(P), 'decay_margin': str(c),
    'residual_h': rows(R), 'normalization': 'h=t/2, 0<=t<=1',
    'basis_order': ['(degree=0,state=0)', '(degree=0,state=1)',
                    '(degree=1,state=0)', '(degree=1,state=1)'],
    'identity': 'R(t/2) = t Z(t)^T G_left Z(t) + (1-t) Z(t)^T G_right Z(t); Z=[I;tI]',
    'bernstein_coefficients': [rows(M) for M in C],
    'G_left': gram_record(Gleft), 'G_right': gram_record(Gright),
    'external_target': 'MatrixSOS.IccLukacsGramCertificateBoundedOdd (d=1) (a=0) (b=1)',
    'external_revision': '02cfe73de3d3535c867eacae5a715036466cab92',
    'caution': 'Check GramIdx and GramTerm basis conventions in the Lean adapter; no external replay performed.'
}
(HERE / 'UNVERIFIED-matrix-gram.json').write_text(json.dumps(result, indent=2) + '\n')
print('Exact symbolic reconstruction and positive LDL pivots passed; formal adapter remains UNVERIFIED.')
