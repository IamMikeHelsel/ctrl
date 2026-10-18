"""Derive rational Bernstein coefficients; Lean independently checks the result."""
import json
from pathlib import Path
import sympy as s
h=s.symbols('h')
A=s.Matrix([[1-h*h,h-s.Rational(3,2)*h*h],[-2*h,1-3*h]])
P=s.Matrix([[5,1],[1,1]])
Q=s.simplify((P-A.T*P*A)/h)
coeff=[Q.diff(h,k).subs(h,0)/s.factorial(k)/2**k for k in range(4)]
B=[sum((coeff[k]*s.binomial(j,k)/s.binomial(3,k) for k in range(j+1)),s.zeros(2)) for j in range(4)]
reconstructed=sum((s.binomial(3,j)*(2*h)**j*(1-2*h)**(3-j)*B[j] for j in range(4)),s.zeros(2))
assert s.simplify(reconstructed-Q)==s.zeros(2)
checks=[]
for b in B:
 r=b-s.eye(2)
 assert r[0,0]>0 and r.det()>0
 checks.append(dict(matrix=[[str(z) for z in row] for row in b.tolist()],
     residual_leading_minor=str(r[0,0]),residual_determinant=str(r.det())))
result=dict(sympy_version=s.__version__,interval='0 <= h <= 1/2',
    certificate='P - A(h)^T P A(h) >= h I',bernstein_coefficients=checks,
    provenance='Exact symbolic discovery. The Sampling.lean proof checks this independently in Lean.')
Path('research/sampling-certificate.json').write_text(json.dumps(result,indent=2))
print(json.dumps(result,indent=2))
