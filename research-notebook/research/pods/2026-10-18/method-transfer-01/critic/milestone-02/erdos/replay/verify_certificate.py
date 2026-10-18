#!/usr/bin/env python3
"""Read-only exact replay, implemented without importing the generator.

Every interval calculation uses rational endpoints. Closed children meet only
on their common boundary. The tree check proves that their union is the root.
This is executable arithmetic evidence, not a Lean/kernel proof.
"""
from fractions import Fraction as Q
from pathlib import Path
import copy
import json

HERE = Path(__file__).resolve().parent


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def neg(a):
    return -a[1], -a[0]


def sub(a, b):
    return add(a, neg(b))


def mul(a, b):
    values = [x*y for x in a for y in b]
    return min(values), max(values)


def div(a, b):
    assert b[0] > 0 or b[1] < 0, 'denominator crosses zero'
    return mul(a, (1/b[1], 1/b[0]))


def square(a):
    hi = max(a[0]**2, a[1]**2)
    lo = 0 if a[0] <= 0 <= a[1] else min(a[0]**2, a[1]**2)
    return Q(lo), hi


def k(x):
    return Q(x), Q(x)


def read(a):
    lo, hi = map(Q, a)
    assert lo <= hi
    return lo, hi


def calculate(y, j):
    r = k(Q(1293, 50000))
    mu = div(mul(k(2), j), y)
    b = sub(y, k(Q(1, 2)))
    assert y[0] > 0 and b[0] > 0
    ell = sub(mul(mul(k(8), r), sub(y, mu)), mul(k(2), mu))
    cee = sub(sub(j, mul(mul(k(4), r), square(sub(y, mu)))), square(mu))
    bee = sub(div(sub(j, r), b), ell)
    ess = sub(add(div(square(bee), k(4)), mul(ell, mu)), cee)
    return cee, ess


def verify(data):
    r, internal = Q(1293, 50000), Q(2, 47)
    low, high, jlow = Q(1559, 2000), Q(781, 1000), Q(423, 10000)
    assert Q(data['R']) == r and Q(data['I']) == internal
    assert data['splits'] == {'c_low': str(low), 'c_high': str(high),
                              'j_low': str(jlow), 'old_c0': '7797/10000'}
    root = ((Q(500, 781), Q(1000, 1559)), (jlow, internal))
    assert read(data['rectangle']['y']) == root[0]
    assert read(data['rectangle']['j']) == root[1]
    assert Q(1, 2) <= low < Q(7797, 10000) < high < Q(4, 5) <= 1
    assert high >= Q(3, 4)
    assert root[0] == (1/(2*high), 1/(2*low))
    p = lambda c: (r-internal-Q(17, 32))*c*c+Q(7, 8)*c+r-Q(3, 8)
    aa, bb, dd = r+Q(1, 4)-internal, Q(3, 8), r+Q(1, 8)
    margins = {'low_cap': r-internal*low*low,
               'low_j': r-high*high*jlow,
               'middle_left': p(high), 'middle_right': p(Q(4, 5)),
               'middle_concavity': -(r-internal-Q(17, 32)),
               'upper_leading': aa, 'upper_discriminant': 4*aa*dd-bb*bb,
               'old_threshold_gap': high-Q(7797, 10000)}
    assert {name: Q(value) for name, value in data['margins'].items()} == margins
    assert all(value > 0 for value in margins.values())
    seen, leaves = set(), []
    nodes = data['cover']

    def visit(index, y, j, depth):
        assert type(index) is int and 0 <= index < len(nodes)
        assert index not in seen, 'repeated child or cycle'
        seen.add(index)
        node = nodes[index]
        assert node['depth'] == depth
        assert read(node['y']) == y and read(node['j']) == j, 'partition gap or overlap'
        cee, ess = calculate(y, j)
        assert read(node['C']) == cee and read(node['S']) == ess, 'wrong enclosure'
        if node['accepted']:
            assert 'children' not in node
            assert cee[1] < 0 and ess[1] <= 0, 'unproved leaf'
            leaves.append(index)
            return
        assert len(node['children']) == 2
        left, right = node['children']
        mid = Q(node['midpoint'])
        if node['axis'] == 'y':
            assert y[0] < mid < y[1]
            visit(left, (y[0], mid), j, depth+1)
            visit(right, (mid, y[1]), j, depth+1)
        else:
            assert node['axis'] == 'j' and j[0] < mid < j[1]
            visit(left, y, (j[0], mid), depth+1)
            visit(right, y, (mid, j[1]), depth+1)

    visit(0, *root, 0)
    assert seen == set(range(len(nodes))), 'unreachable certificate nodes'
    assert len(leaves) == data['leaf_count'] == 272
    assert max(node['depth'] for node in nodes) == data['max_depth'] == 9
    assert Q(data['largest_leaf_C_upper']) == max(Q(nodes[i]['C'][1]) for i in leaves)
    assert Q(data['largest_leaf_S_upper']) == max(Q(nodes[i]['S'][1]) for i in leaves)
    # Nonoverlap is in interiors; shared closed endpoints are intentional.
    for pos, aidx in enumerate(leaves):
        a = nodes[aidx]
        ay, aj = read(a['y']), read(a['j'])
        for bidx in leaves[pos+1:]:
            b = nodes[bidx]
            by, bj = read(b['y']), read(b['j'])
            assert max(ay[0], by[0]) >= min(ay[1], by[1]) or max(aj[0], bj[0]) >= min(aj[1], bj[1])
    area = sum((read(nodes[i]['y'])[1]-read(nodes[i]['y'])[0]) *
               (read(nodes[i]['j'])[1]-read(nodes[i]['j'])[0]) for i in leaves)
    assert area == (root[0][1]-root[0][0])*(root[1][1]-root[1][0])
    fail = data['failed_broad_window']
    assert Q(fail['witness_c']) == Q(79, 100)
    y, j = Q(fail['witness_y']), Q(fail['witness_j'])
    assert y == Q(50, 79) and j == internal
    cee, ess = calculate(k(y), k(j))
    assert cee[0] == cee[1] < 0 < ess[0] == ess[1]
    assert Q(fail['point']['C']) == cee[0] and Q(fail['point']['S']) == ess[0]
    assert Q(fail['old_middle_margin']) == p(Q(79, 100)) > 0
    return {'nodes': len(nodes), 'leaves': len(leaves), 'exact_area': str(area),
            'max_depth': data['max_depth'], 'all_margins_positive': True,
            'interiors_disjoint': True, 'entire_rectangle_covered': True}


def main():
    data = json.loads((HERE/'certificate.json').read_text())
    result = verify(data)
    mutants = []
    for name in ['missing_child', 'false_S_enclosure', 'wrong_rectangle', 'lower_target']:
        bad = copy.deepcopy(data)
        if name == 'missing_child':
            bad['cover'][0]['children'] = bad['cover'][0]['children'][:1]
        elif name == 'false_S_enclosure':
            index = next(i for i, node in enumerate(bad['cover']) if node['accepted'])
            bad['cover'][index]['S'][1] = '0'
        elif name == 'wrong_rectangle':
            bad['rectangle']['y'][0] = '1/2'
        else:
            bad['R'] = '1/50'
        try:
            verify(bad)
        except (AssertionError, ValueError):
            mutants.append({'name': name, 'rejected': True})
        else:
            raise AssertionError('negative control was accepted: '+name)
    print(json.dumps({'passed': True, 'certificate': result, 'negative_controls': mutants}, indent=2))


if __name__ == '__main__':
    main()
