"""Exact tests of one DECLARED candidate for GU (9.3), not the author's selection.

No floating point arithmetic, numerical Clifford matrices, or external packages.
Coefficients are Gaussian rationals; both algebra products use bit-mask bases.
Run from any directory. The JSON result is printed to stdout.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations
import json


@dataclass(frozen=True)
class G:
    r: F = F(0)
    i: F = F(0)

    def __add__(self, other):
        other = scalar(other)
        return G(self.r + other.r, self.i + other.i)

    __radd__ = __add__

    def __neg__(self):
        return G(-self.r, -self.i)

    def __sub__(self, other):
        return self + -scalar(other)

    def __mul__(self, other):
        other = scalar(other)
        return G(self.r * other.r - self.i * other.i,
                 self.r * other.i + self.i * other.r)

    __rmul__ = __mul__

    def __bool__(self):
        return bool(self.r or self.i)

    def conj(self):
        return G(self.r, -self.i)

    def out(self):
        return [str(self.r), str(self.i)]


def scalar(x):
    return x if isinstance(x, G) else G(F(x))


IM = G(F(0), F(1))


def add_term(out, key, value):
    value = out.get(key, G()) + value
    if value:
        out[key] = value
    elif key in out:
        del out[key]


class Model:
    def __init__(self, signs):
        self.signs = tuple(signs)
        self.n = len(signs)
        self.top = (1 << self.n) - 1
        self.pairs = list(combinations(range(self.n), 2))

    def metric(self, mask):
        out = 1
        for a, s in enumerate(self.signs):
            if mask & (1 << a):
                out *= s
        return out

    def reorder(self, left, right):
        swaps = sum((right & ((1 << a) - 1)).bit_count()
                    for a in range(self.n) if left & (1 << a))
        return (-1) ** swaps

    def clifford(self, left, right):
        return left ^ right, self.reorder(left, right) * self.metric(left & right)

    def hodge(self, form):
        """S convention: alpha wedge S(beta) = <alpha,beta> volume."""
        out = {}
        for (ext, cl), value in form.items():
            comp = self.top ^ ext
            add_term(out, (comp, cl), value * self.reorder(ext, comp) * self.metric(ext))
        return out

    def prod(self, a, b, kind):
        """Exterior wedge, with fibre product mul / comm / J=i anticommutator."""
        out = {}
        for (ae, ac), av in a.items():
            for (be, bc), bv in b.items():
                if ae & be:
                    continue
                mask, sign = self.clifford(ac, bc)
                factor = scalar(sign)
                if kind != 'mul':
                    _, reverse = self.clifford(bc, ac)
                    factor = scalar(sign - reverse) if kind == 'comm' else IM * (sign + reverse)
                add_term(out, (ae | be, mask), av * bv * self.reorder(ae, be) * factor)
        return out

    def adjoint(self, form):
        """Antilinear Clifford conjugation on fibre coefficients only."""
        return {(e, c): v.conj() * (-1) ** (c.bit_count() * (c.bit_count() + 1) // 2)
                for (e, c), v in form.items()}

    def skew(self, form):
        return self.adjoint(form) == {k: -v for k, v in form.items()}

    def phi(self, degree):
        return {(sum(1 << a for a in ids), sum(1 << a for a in ids)): G(F(1))
                for ids in combinations(range(self.n), degree)}

    def curvature(self, R):
        out = {}
        for a, b in self.pairs:
            for c, d in self.pairs:
                value = R(a, b, c, d)
                if value:
                    out[((1 << a) | (1 << b), (1 << c) | (1 << d))] = scalar(
                        value * self.signs[c] * self.signs[d])
        return out

    def ricci(self, R):
        return [[sum(self.signs[a] * R(a, b, a, d) for a in range(self.n))
                 for d in range(self.n)] for b in range(self.n)]

    def sharp_form(self, tensor):
        return {(1 << b, 1 << d): scalar(self.signs[d] * tensor[b][d])
                for b in range(self.n) for d in range(self.n) if tensor[b][d]}

    def test(self, name, R, algebraic=True):
        phi1, phi2, curv = self.phi(1), self.phi(2), self.curvature(R)
        ric = self.ricci(R)
        scal = sum(self.signs[b] * ric[b][b] for b in range(self.n))
        einstein = [[ric[b][d] - (F(1, 2) * scal * self.signs[b] if b == d else 0)
                     for d in range(self.n)] for b in range(self.n)]
        first = self.prod(phi1, self.hodge(curv), 'comm')
        inner = self.hodge(self.prod(phi2, self.hodge(curv), 'J'))
        second = self.hodge(self.prod(phi1, inner, 'J'))
        candidate = dict(first)
        for key, value in second.items():
            add_term(candidate, key, value * F(-1, 2))
        expected_first = {k: -2 * v for k, v in self.hodge(self.sharp_form(ric)).items()}
        expected_inner = {} if scal == 0 else {(0, 0): -IM * self.metric(self.top) * scal}
        expected_einstein = {k: -2 * v for k, v in self.hodge(self.sharp_form(einstein)).items()}
        symmetry_failures = [0, 0, 0, 0]
        for a in range(self.n):
            for b in range(self.n):
                for c in range(self.n):
                    for d in range(self.n):
                        vals = [R(a,b,c,d)+R(b,a,c,d), R(a,b,c,d)+R(a,b,d,c),
                                R(a,b,c,d)-R(c,d,a,b),
                                R(a,b,c,d)+R(a,c,d,b)+R(a,d,b,c)]
                        symmetry_failures = [x + bool(y) for x,y in zip(symmetry_failures,vals)]
        out = {'name':name, 'signature':list(self.signs), 'algebraic_curvature_expected':algebraic,
               'symmetry_failure_counts_antisym1_antisym2_pairswap_bianchi':symmetry_failures,
               'ricci_zero':not any(any(row) for row in ric), 'scalar':str(scal),
               'first_equals_minus_two_hodge_ricci':first == expected_first,
               'inner_equals_minus_i_determinant_scalar':inner == expected_inner,
               'candidate_equals_minus_two_hodge_einstein':candidate == expected_einstein,
               'curvature_nonzero_terms':len(curv), 'candidate_nonzero_terms':len(candidate),
               'phi1_skew':self.skew(phi1), 'phi2_skew':self.skew(phi2),
               'curvature_skew':self.skew(curv), 'first_skew':self.skew(first),
               'inner_skew':self.skew(inner), 'second_skew':self.skew(second),
               'candidate_skew':self.skew(candidate)}
        if not algebraic:
            out['inner_terms'] = [{'exterior_mask':e,'clifford_mask':c,'coefficient':v.out()}
                                  for (e,c),v in sorted(inner.items())]
        return out


def diagonal_R(weights):
    def R(a,b,c,d):
        if a == b or c == d:
            return 0
        if {a,b} != {c,d}:
            return 0
        return weights.get(tuple(sorted((a,b))),0) * (1 if (a<b)==(c<d) else -1)
    return R


def kulkarni(g,h):
    return lambda a,b,c,d: g[a][c]*h[b][d]+g[b][d]*h[a][c]-g[a][d]*h[b][c]-g[b][c]*h[a][d]


def main():
    model = Model([1]*7+[-1]*7)
    n = model.n
    g = [[model.signs[a] if a==b else 0 for b in range(n)] for a in range(n)]
    h = [[((a+1)*(b+1) % 7)-3 for b in range(n)] for a in range(n)]
    cases = [model.test('constant_curvature',diagonal_R({(a,b):model.signs[a]*model.signs[b] for a,b in model.pairs})),
             model.test('kulkarni_nomizu_g_h',kulkarni(g,h)),
             model.test('nonzero_weyl_four_positive_directions',diagonal_R({(0,1):1,(2,3):1,(0,2):-1,(1,3):-1})),
             model.test('nonzero_weyl_mixed_directions',diagonal_R({(0,1):1,(7,8):1,(0,7):1,(1,8):1}))]
    # Four-form component is pair symmetric and pair antisymmetric but fails Bianchi.
    # This fixture prevents using only the first three symmetries for the scalar claim.
    def fourform(a,b,c,d):
        ids=(a,b,c,d)
        if set(ids) != {0,1,2,3}:
            return 0
        return (-1)**sum(ids[x]>ids[y] for x in range(4) for y in range(x+1,4))
    cases.append(model.test('bianchi_negative_control',fourform,False))
    # This is an exact finite check, not a proof for all curvature tensors.
    assertions = all(c['first_equals_minus_two_hodge_ricci'] and c['inner_equals_minus_i_determinant_scalar']
                     and c['candidate_equals_minus_two_hodge_einstein'] and c['candidate_skew']
                     and c['symmetry_failure_counts_antisym1_antisym2_pairswap_bianchi']==[0]*4
                     for c in cases[:-1])
    assertions &= (not cases[-1]['inner_equals_minus_i_determinant_scalar']
                   and cases[-1]['symmetry_failure_counts_antisym1_antisym2_pairswap_bianchi'][3] > 0)
    print(json.dumps({'status':'pass' if assertions else 'FAIL','arithmetic':'Gaussian rationals',
                      'scope':'exact selected fixtures, not a universal proof','cases':cases},indent=2))
    assert assertions


if __name__ == '__main__':
    main()
