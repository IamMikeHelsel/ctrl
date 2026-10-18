#!/usr/bin/env python3
"""Reproduce the rational vertices of the normalized actuator-lag enclosure.

This symbolic calculation is untrusted preparation. ActuatorLag.lean separately
checks the exact exponential ODE segments, enclosure, and generated-model bridges.
The endpoints are not claimed to be exact actuator-lag transition matrices.
"""
import json
from pathlib import Path
import sympy as s

PROJECT = Path(__file__).resolve().parents[1]


def main():
    h, e = s.symbols('h e')
    # x'=v, v'=a, a'=-a+u; u is sampled once as -x0-3v0-2a0.
    F = s.Matrix([[1,h,h-1+e],[0,1,1-e],[0,0,e]])
    G = s.Matrix([h*h/2-h+1-e,h-1+e,1-e])
    A = F-G*s.Matrix([[1,3,2]])
    P = json.loads((PROJECT/'benchmarks/jerk-integrator.json').read_text())['P']
    for slug, E in [('lower',1-h),('upper',1-h+h*h)]:
        B = s.expand(A.subs(e,E))
        degree = max(s.degree(q,h) for q in B)
        coefficients = [[[str(s.expand(B[i,j]).coeff(h,k)) for j in range(3)]
                         for i in range(3)] for k in range(degree+1)]
        expected = json.loads((PROJECT/f'benchmarks/actuator-lag-{slug}.json').read_text())
        assert expected['P'] == P
        assert expected['A_coefficients'] == coefficients
        assert expected['partition'] == ['0','1/5']
        assert expected['decay_margin'] == '1'
        print(f'{slug}: symbolic vertex matches stored rational input (UNVERIFIED until Lean).')


if __name__ == '__main__':
    main()
