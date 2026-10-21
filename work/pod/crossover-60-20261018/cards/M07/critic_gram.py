"""Independent exact Gram factors and determinant/rank negative controls."""

import hashlib
import json
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path

HERE = Path(__file__).resolve().parent
PDF = Path(
    "/Users/mike/Documents/Codex/2026-10-18/do-more-work-with-a-team/exploration/sources/thesis-1992.pdf"
)
assert (
    hashlib.sha256(PDF.read_bytes()).hexdigest()
    == "11cb75f7edcd7f2371271f672e69d978189a11dd8c94f2cc5df3546b4abcaea7"
)


def det(matrix):
    a = [list(map(F, row)) for row in matrix]
    ans = F(1)
    for k in range(len(a)):
        p = next((i for i in range(k, len(a)) if a[i][k]), None)
        if p is None:
            return F(0)
        if p != k:
            a[p], a[k] = a[k], a[p]
            ans = -ans
        pivot = a[k][k]
        ans *= pivot
        for i in range(k + 1, len(a)):
            c = a[i][k] / pivot
            for j in range(k + 1, len(a)):
                a[i][j] -= c * a[k][j]
    return ans


def gram(vectors):
    return [[sum(x.get(k, 0) * v for k, v in y.items()) for y in vectors] for x in vectors]


def difference_basis(terms):
    vectors = []
    for a, b in zip(terms[:-1], terms[1:], strict=True):
        v = dict(a)
        for k, x in b.items():
            v[k] = v.get(k, 0) - x
        vectors.append({k: x for k, x in v.items() if x})
    return vectors


blocks = []
# Signed term order does not change determinant of the difference-basis Gram.
for d in (3, 4, 5, 6, 7, 8):
    terms = [{("atom", i): F((-1) ** i)} for i in range(d)]
    G = gram(difference_basis(terms))
    assert det(G) == d
    blocks.append({"term_count": d, "gram": G, "det": det(G)})
# Target Y3 support partitions are disjoint: i absent from residual triple for
# shift, versus i present in residual triple for raise.
shift = []
for quad in combinations(range(8), 4):
    shift.append([{(i, tuple(j for j in quad if j != i)): F(1)} for i in quad])
raise_blocks = []
for pair in combinations(range(8), 2):
    raise_blocks.append(
        [{(i, tuple(sorted(pair + (i,)))): F(1)} for i in range(8) if i not in pair]
    )
all_blocks = shift + raise_blocks
supports = [set().union(*(set(t) for t in block)) for block in all_blocks]
assert len(set().union(*supports)) == sum(map(len, supports)) == 448
assert sum(len(block) - 1 for block in all_blocks) == 350
GY3 = F(1)
for block in all_blocks:
    GY3 *= det(gram(difference_basis(block)))
assert GY3 == 2**168 * 3**28
# L4+ chooses four-subsets of1..7; every normalized self-dual blade has norm²1/2.
l4 = list(combinations(range(7), 4))
assert len(l4) == 35
GL4 = F(1, 2) ** 35
# Y1:28 disjoint symmetric off-diagonal pairs norm²2, plus7 diagonal differences.
GY1 = 2**28 * det(gram(difference_basis([{("diag", i): F(1)} for i in range(8)])))
assert GY1 == 2**31
GT = GL4 * GY3 * GY1
assert GT == 2**164 * 3**28
# Explicit nonorthonormal target basis B=diag(2,1), mapI, source standard.
coordinate = [[F(1, 2), 0], [0, 1]]
pairing = [[2, 0], [0, 1]]
assert det(pairing) == 4 * det(coordinate)
# Modular rank loss alone cannot certify rational singularity.
assert det([[101, 0], [0, 1]]) == 101 and det([[0, 0], [0, 1]]) == 0
# Full matrix sign is invisible to all448x448 determinants.
assert (-1) ** 448 == 1
fixtures = json.loads(
    Path(
        "/Users/mike/Dev/ctrl-research-notebook/research-notebook/publication/gu-source-exploration-20261018/software/thesis-appendix/determinant-fixtures.json"
    ).read_text()
)
residues = []
for r in fixtures["fixtures"]:
    d = r["determinant_sign"]
    for prime, power in r["prime_factorization_abs"].items():
        d *= int(prime) ** power
    residues.append(
        {
            "label": r["label"],
            "source_determinant_mod101": d % 101,
            "unscaled_m_determinant_mod101": d * pow(pow(2, 448, 101), -1, 101) % 101,
        }
    )
assert (
    all(r["source_determinant_mod101"] for r in residues[:5])
    and residues[-1]["source_determinant_mod101"] == 0
)
out = {
    "source_pdf_hash_verified": True,
    "target_dimension": 448,
    "Y3_dimension": 350,
    "target_Gram_factors": {
        "L4p": "2^-35",
        "Y3": "2^168*3^28",
        "L2": "1",
        "Y1": "2^31",
        "product": "2^164*3^28",
    },
    "Gram_small_blocks": blocks,
    "fixture_residues": residues,
    "negative_controls": {
        "coordinate_vs_pairing_determinants": [str(det(coordinate)), str(det(pairing))],
        "rational_invertible_but_singular_mod101": [[101, 0], [0, 1]],
        "global_minus_sign_invisible_in_even_dimension": True,
    },
    "scope": "Exact Gram blocks and support partitions of scanned target-basis recipes; not the symbol matrix or its determinant. Fixture residues are computed from source-reported factorizations, not from a reconstructed matrix. Basis pairing-to-coordinate comparison assumes output lies in the declared target space.",
}
(HERE / "critic_gram.json").write_text(json.dumps(out, default=str, indent=2) + "\n")
print(json.dumps({k: v for k, v in out.items() if k != "Gram_small_blocks"}, indent=2))
