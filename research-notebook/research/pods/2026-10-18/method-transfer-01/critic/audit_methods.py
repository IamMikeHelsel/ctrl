"""Independent metadata audit and small exact transfer counter-controls.

This does not execute external code or validate the source papers' theorems.
Run from any directory with Python 3; writes only beside this script.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import product
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
CORPUS = HERE.parent / 'corpus'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
source = json.loads((CORPUS / 'source-manifest.json').read_text())
checked = []
for item in source['files']:
    path = CORPUS / item['path']
    assert sha(path) == item['sha256'], path
    checked.append(item['path'])

# Line parsing deliberately handles the parenthesis inside CAT(0)'s filename.
lines = (CORPUS / 'CONTENTS.md').read_text().splitlines()
ids, papers, docs = [], [], []
for line in lines:
    head = re.match(r'^\*\*(\d{3})\.', line)
    if head:
        ids.append(head[1])
    if line.startswith('&emsp;[') and '](preprints/' in line:
        target = line.split('](preprints/', 1)[1]
        assert '.pdf)' in target, line
        papers.append('preprints/' + target.rsplit('.pdf)', 1)[0] + '.pdf')
    docs.extend(re.findall(r'\[Lean\]\((lean/docs/[^)]+)\)', line))
assert len(ids) == len(set(ids)) == 372
assert len(papers) == len(set(papers)) == 719
assert len(docs) == len(set(docs)) == 242
preprints = json.loads((CORPUS / 'preprints-tree.json').read_text())
lean_docs = json.loads((CORPUS / 'lean-docs-tree.json').read_text())
reasoning = json.loads((CORPUS / 'reasoning_traces-tree.json').read_text())
assert not any(t.get('truncated') for t in (preprints, lean_docs, reasoning))
preprint_paths = {'preprints/' + x['path'] for x in preprints['tree']}
doc_paths = {'lean/docs/' + x['path'] for x in lean_docs['tree']}
assert set(papers) <= preprint_paths
assert set(docs) <= doc_paths
readme = (CORPUS / 'README.md').read_text()
trace_links = re.findall(r'\]\((reasoning_traces/[^)]+\.pdf)\)', readme)
assert len(trace_links) == len(set(trace_links)) == 10
assert set(trace_links) <= {'reasoning_traces/' + x['path'] for x in reasoning['tree']}
family_index = json.loads((CORPUS / 'family-index.json').read_text())
assert set(ids) == {f['id'] for f in family_index['families']}
assert set(papers) == {p['path'] for f in family_index['families'] for p in f['papers']}
assert set(docs) == {p for f in family_index['families'] for p in f['lean_documentation_paths']}
broad_tree = json.loads((CORPUS / 'tree.json').read_text())
assert broad_tree['truncated'] is True

# Three pair marginals: each bit fair, each pair always different.
# Every triple contains an equal pair; no probability measure can realize all three.
assignments = list(product((0, 1), repeat=3))
valid = [a for a in assignments if all(a[i] != a[j] for i,j in ((0,1),(1,2),(0,2)))]
assert valid == []
gram = [[1 if i == j else -1 for j in range(3)] for i in range(3)]
quadratic_form_ones = sum(map(sum, gram))
assert quadratic_form_ones == -3

# GF(4) = F2[z]/(z^2+z+1), encoded by two bits. No approximate arithmetic.
def mul(a, b):
    value = 0
    for _ in range(2):
        if b & 1:
            value ^= a
        b >>= 1
        a <<= 1
        if a & 4:
            a ^= 7
    return value

def power(a, k):
    out = 1
    for _ in range(k):
        out = mul(out, a)
    return out

def field_sum(xs):
    out = 0
    for x in xs:
        out ^= x
    return out

power_sums = [field_sum(power(a, k) for a in range(4)) for k in range(4)]
assert power_sums == [0, 0, 0, 1]
real_constant_sum = sum(Q(1) for _ in range(4))
assert real_constant_sum == 4

# Bounded martingale: information is trivial until the final Rademacher reveal.
# Expected squared increments have total 1 and average 1/L; the last is 1.
L = 100
energies = [Q(0)] * (L - 1) + [Q(1)]
assert sum(energies) / L == Q(1, L)
assert max(energies) == 1

out = {
    'revision': source['revision'],
    'scope': 'Metadata consistency and exact toy counter-controls; no external theorem replay.',
    'metadata': {
        'manifest_files_verified': checked,
        'families': len(ids), 'manuscript_links': len(papers),
        'family_lean_doc_links': len(docs), 'reasoning_summary_links': len(trace_links),
        'complete_subtree_cross_checks': True, 'broad_tree_is_truncated': True,
        'root_family_index_agrees': True,
        'input_hashes': {p: sha(CORPUS / p) for p in (
            'source-manifest.json', 'CONTENTS.md', 'README.md', 'history.md',
            'preprints-tree.json', 'lean-docs-tree.json', 'reasoning_traces-tree.json',
            'family-index.json', 'inventory-summary.json')},
    },
    'counter_controls': {
        'pairwise_marginals': {
            'compatible_triples': valid,
            'ones_gram_quadratic_form': quadratic_form_ones,
            'conclusion': 'Marginal consistency alone fails; BasicSDP would reject this non-PSD Gram matrix. This is not an SDP counterexample.',
        },
        'finite_field_line_sum': {
            'GF4_power_sums_degrees_0_to_3': power_sums,
            'real_constant_sum': str(real_constant_sum),
            'conclusion': 'q-2 degree cap and field arithmetic matter. This tests only the line-sum identity, not the hypergraph or group-ring construction.',
        },
        'averaged_martingale_energy': {
            'levels': L, 'mean_increment_energy': str(sum(energies) / L),
            'max_increment_energy': str(max(energies)),
            'conclusion': 'An average O(1/L) level error does not bound every level by O(1/L). No deterministic timing guarantee follows.',
        },
    },
    'all_checks_pass': True,
}
(HERE / 'method-audit-results.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps({'families':len(ids), 'manuscripts':len(papers), 'toy_controls':3, 'all_checks_pass':True}))
