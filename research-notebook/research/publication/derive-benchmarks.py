#!/usr/bin/env python3
"""Derive two exact held-input benchmarks, without writing generated Lean.

Run from the workspace using .tools/research-python/bin/python. Default mode
checks the committed JSON; --write replaces only the two owned benchmark JSONs.
The SymPy/LDL checks are producer evidence, not Lean verification.

State convention: z' = N z + B u, and u = -K z(0) is held for the segment.
For nilpotent N, F(h) = exp(hN) - integral_0^h exp(sN) ds B K is a finite
polynomial. Thus F'(h) = N F(h) - B K, NOT (N-BK) F(h). The latter would
continuously recompute feedback and describe a different sampled controller.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path

import sympy as sp

ROOT = Path(__file__).resolve().parents[2]
GENERATOR = ROOT / 'lean-controls/scripts/generate_interval_certificate.py'
BENCHMARKS = ROOT / 'lean-controls/benchmarks'


def strings(matrix):
    return [[str(x) for x in row] for row in matrix.tolist()]


def load_generator():
    spec = importlib.util.spec_from_file_location('interval_producer', GENERATOR)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def plants():
    N = sp.Matrix([[0, 1, 0], [0, 0, 1], [0, 0, 0]])
    B = sp.Matrix([0, 0, 1])
    K = sp.Matrix([[1, 3, 3]])
    yield {
        'name': 'JerkIntegrator', 'file': 'jerk-integrator.json',
        'description': 'Exact zero-order-held jerk integrator; u=-x-3v-3a',
        'state_order': ['position', 'velocity', 'acceleration'],
        'N': N, 'B': B, 'K': K, 'upper': sp.Integer(24),
        'partition': ['0', '1/2'],
    }
    N = sp.zeros(4)
    N[0, 2] = 1
    N[1, 3] = 1
    B = sp.Matrix([[0, 0], [0, 0], [1, 0], [0, 1]])
    Kp = sp.Matrix([[2, sp.Rational(1, 2)], [sp.Rational(1, 2), 1]])
    Kd = sp.Matrix([[3, sp.Rational(1, 4)], [sp.Rational(1, 4), 2]])
    assert Kp * Kd != Kd * Kp
    yield {
        'name': 'CoupledPlanar', 'file': 'coupled-planar.json',
        'description': 'Exact zero-order-held planar double integrator with noncommuting proportional and derivative gains',
        'state_order': ['q1', 'q2', 'v1', 'v2'],
        'N': N, 'B': B, 'K': Kp.row_join(Kd), 'upper': sp.Integer(10),
        'partition': ['0', '1/4', '1/2'],
        'coupling': 'Kp*Kd-Kd*Kp=[[0,-1/4],[1/4,0]]; the symmetric gains cannot be simultaneously orthogonally diagonalized',
    }


def derive(plant, producer):
    N, B, K = (plant[key] for key in ('N', 'B', 'K'))
    n = N.rows
    h = sp.Symbol('h')
    assert N**n == sp.zeros(n)
    F = sp.eye(n)
    for k in range(1, n + 1):
        F += h**k / sp.factorial(k) * (N**k - N**(k - 1) * B * K)
    F = F.applyfunc(sp.expand)
    assert F.subs(h, 0) == sp.eye(n)
    assert (F.diff(h) - N * F + B * K).applyfunc(sp.expand) == sp.zeros(n)

    Ac = N - B * K
    unknown = sp.Matrix(n, n, lambda i, j: sp.Symbol(f'p{min(i,j)}_{max(i,j)}'))
    solutions = sp.solve(list(Ac.T * unknown + unknown * Ac + 4 * sp.eye(n)),
                         sorted(unknown.free_symbols, key=str), dict=True)
    if len(solutions) != 1:
        raise ValueError('Expected a unique exact Lyapunov solution.')
    P = unknown.subs(solutions[0])
    assert not P.free_symbols
    assert Ac.T * P + P * Ac == -4 * sp.eye(n)
    _, p_pivots = producer.ldl(P)
    assert all(d > 0 for d in p_pivots)
    lower = sp.Rational(1, 4)
    producer.ldl(P - lower * sp.eye(n))
    producer.ldl(plant['upper'] * sp.eye(n) - P)

    degree = max(int(sp.Poly(entry, h).degree()) for entry in F if entry != 0)
    coefficients = [F.applyfunc(lambda entry: sp.Poly(entry, h).nth(k))
                    for k in range(degree + 1)]
    model = {
        'state_order': plant['state_order'],
        'equation': "z'=N*z+B*u; u=-K*z_at_sample is held throughout each sample interval",
        'N': strings(N), 'B': strings(B), 'K': strings(K),
        'transition_identity': "F(0)=I and F'(h)=N*F(h)-B*K",
        'continuous_design_identity': '(N-B*K)^T*P+P*(N-B*K)=-4*I',
        'normalization': 'All coordinates and time are mathematical normalized quantities; no calibrated hardware model is claimed.',
    }
    if 'coupling' in plant:
        model['coupling'] = plant['coupling']
    data = {
        'description': plant['description'],
        'A_coefficients': [strings(C) for C in coefficients],
        'P': strings(P),
        'decay_margin': '1',
        'partition': plant['partition'],
        'model': model,
        'producer_checked_energy_bounds': {'lower': str(lower), 'upper': str(plant['upper'])},
        'verification_status': 'Exact producer checks only. Generated Lean and the held-model correspondence require independent checking.',
    }
    # Calling produce performs its exact reconstruction/LDL checks. Its returned
    # Lean text is intentionally not written by this benchmark derivation.
    text, evidence = producer.produce(data, plant['name'])
    pivots = [sp.Rational(d) for segment in evidence['segments']
              for coefficient in segment['coefficients'] for d in coefficient['d']]
    summary = {
        'file': plant['file'], 'dimension': n, 'transition_degree': degree,
        'residual_degree': evidence['degree'], 'partition': plant['partition'],
        'positive_P_pivots': [str(d) for d in p_pivots],
        'minimum_residual_coefficient_pivot': str(min(pivots)),
        'generated_lean_characters_not_written': len(text),
        'status': 'PRODUCER CHECKS PASSED; LEAN NOT RUN BY THIS SCRIPT',
    }
    return data, summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    producer = load_generator()
    summaries = []
    for plant in plants():
        data, summary = derive(plant, producer)
        path = BENCHMARKS / plant['file']
        if args.write:
            path.write_text(json.dumps(data, indent=2) + '\n')
        else:
            if json.loads(path.read_text()) != data:
                raise ValueError(f'Derivation differs from committed JSON: {path}')
        summaries.append(summary)
    print(json.dumps(summaries, indent=2))


if __name__ == '__main__':
    main()
