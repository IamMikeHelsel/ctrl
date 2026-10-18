#!/usr/bin/env python3
"""Adversarial producer checks. --lean additionally tests the kernel boundary.

These tests do not certify the producer; only checking the emitted statements
with Lean establishes their proofs. Run from any directory.
"""
from __future__ import annotations
import argparse
import copy
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from lean_runtime import runtime

SCRIPT = Path(__file__).with_name('generate_interval_certificate.py')
PROJECT = SCRIPT.parent.parent
WORKSPACE = PROJECT.parent
spec = importlib.util.spec_from_file_location('producer_under_test', SCRIPT)
producer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(producer)

BASE = {'P': [[1]], 'A_coefficients': [[[1]], [[-1]]],
        'decay_margin': 1, 'partition': [0, '1/2']}


class ProducerChecks(unittest.TestCase):
    def changed(self, **kw):
        data = copy.deepcopy(BASE)
        data.update(kw)
        return data

    def reject(self, data):
        with self.assertRaises((ValueError, TypeError, KeyError)):
            producer.produce(data, 'Adversarial')

    def test_valid_exact_input(self):
        code, evidence = producer.produce(BASE, 'Scalar')
        self.assertEqual(evidence['dimension'], 1)
        self.assertIn('theorem certified_decrease', code)
        self.assertNotIn('sorry', code)
        self.assertNotIn('admit', code)
        self.assertEqual(evidence['segments'][0]['coefficients'][0]['C'], [['1']])
        self.assertEqual(evidence['segments'][0]['coefficients'][-1]['C'], [['1/2']])

    def test_negative_energy_cannot_be_lyapunov_certificate(self):
        # V=-x² decreases for unstable x+=(1+h)x. Positive energy is essential.
        self.reject(self.changed(P=[[-1]], A_coefficients=[[[1]], [[1]]]))

    def test_singular_energy_rejected(self):
        self.reject(self.changed(P=[[0]]))

    def test_float_bool_and_expression_rejection(self):
        for value in [0.1, True, '0.1', '1/0', '1/-2', 'sqrt(2)',
                      '__import__("os").system("touch /tmp/not-executed")']:
            with self.subTest(value=value):
                self.reject(self.changed(P=[[value]]))

    def test_invalid_shape(self):
        for rows in [[], [1], [[1, 0]], [[1], [0]], [[1, 0], [0]]]:
            with self.subTest(rows=rows):
                self.reject(self.changed(P=rows))
        self.reject(self.changed(A_coefficients=[[[1, 0], [0, 1]]]))

    def test_nonsymmetric_energy(self):
        self.reject(self.changed(P=[[1, 1], [0, 1]],
                                 A_coefficients=[[[1, 0], [0, 1]]]))

    def test_invalid_partition(self):
        for partition in [[], [0], [-1, 0], [0, 0], [1, 0], [0, 1, '1/2']]:
            with self.subTest(partition=partition):
                self.reject(self.changed(partition=partition))

    def test_invalid_decay(self):
        for margin in [0, -1, '0/3', 0.1, True]:
            with self.subTest(margin=margin):
                self.reject(self.changed(decay_margin=margin))

    def test_missing_identity_at_zero(self):
        self.reject(self.changed(A_coefficients=[]))
        self.reject(self.changed(A_coefficients=[[[2]], [[-1]]]))

    def test_negative_residual_rejected(self):
        self.reject(self.changed(A_coefficients=[[[1]], [[1]]]))
        self.reject(self.changed(partition=[0, 2]))

    def test_ldl_negative_and_zero_pivot_rejected(self):
        for rows in [[[-1]], [[0, 1], [1, 0]], [[1, 2], [2, 1]]]:
            with self.subTest(rows=rows), self.assertRaises(ValueError):
                producer.ldl(producer.sp.Matrix(rows))

    def test_ldl_singular_psd_supported(self):
        for rows in [[[0]], [[1, 1], [1, 1]], [[0, 0], [0, 2]]]:
            a = producer.sp.Matrix(rows)
            L, d = producer.ldl(a)
            self.assertTrue(all(v >= 0 for v in d))
            self.assertEqual(L * producer.sp.diag(*d) * L.T, a)

    def test_namespace_injection_rejected(self):
        for name in ['bad', '../Bad', 'Bad\naxiom unsound : False', 'Bad;#eval 1']:
            with self.subTest(name=name), self.assertRaises(ValueError):
                producer.produce(BASE, name)

    def test_cli_does_not_claim_lean_verification(self):
        with tempfile.TemporaryDirectory(prefix='certificate-producer-') as directory:
            p = Path(directory)
            (p/'input.json').write_text(json.dumps(BASE))
            result = subprocess.run([sys.executable, str(SCRIPT), str(p/'input.json'),
                                     '--output', str(p/'Output.lean'), '--name', 'Scalar'],
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            status = json.loads(result.stdout)
            self.assertIn('UNVERIFIED', status['status'])
            self.assertTrue((p/'Output.lean').exists())


def lean_boundary_check():
    lake, env = runtime(PROJECT)
    code, _ = producer.produce(BASE, 'KernelBoundary')
    # Change a supplied residual coefficient but leave its LDL reconstruction
    # and the model identity unchanged. Checking must reject the false witness.
    needle = 'def s0c0 : Mat := ' + producer.mat_literal(producer.sp.Matrix([[1]]))
    if needle not in code:
        raise AssertionError('Expected scalar coefficient absent; adapt mutation test.')
    corrupt = code.replace(needle, 'def s0c0 : Mat := ' + producer.mat_literal(producer.sp.Matrix([[-1]])), 1)
    lines = code.splitlines()
    transition_line = next(line for line in lines if line.startswith('def transition '))
    corrupt_model = code.replace(transition_line, 'def transition (h : ℝ) : Mat := !![1 + h]', 1)
    with tempfile.TemporaryDirectory(prefix='certificate-kernel-') as directory:
        for label, text, success in [('valid', code, True), ('corrupt', corrupt, False),
                                     ('corrupt_model', corrupt_model, False)]:
            path = Path(directory)/f'{label}.lean'
            path.write_text(text)
            result = subprocess.run([str(lake), 'env', 'lean', str(path)], cwd=PROJECT,
                                    env=env, capture_output=True, text=True, timeout=180)
            if (result.returncode == 0) != success:
                raise AssertionError(f'{label}: unexpected Lean status {result.returncode}\n'
                                     +result.stdout+result.stderr)
            print(f'Lean boundary check {label}: ' + ('accepted' if success else 'rejected'))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', action='store_true', help='Compile valid and corrupted artifacts')
    args = parser.parse_args()
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(ProducerChecks)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    if not result.wasSuccessful():
        raise SystemExit(1)
    if args.lean:
        lean_boundary_check()
