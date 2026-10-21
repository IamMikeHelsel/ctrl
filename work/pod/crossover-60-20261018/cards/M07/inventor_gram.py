"""Independent exact target-basis Gram audit, not the dissertation symbol matrix."""

import json
from fractions import Fraction as F
from itertools import combinations
from math import prod
from pathlib import Path


def sign(indices):
    return (-1) ** sum(a > b for i, a in enumerate(indices) for b in indices[i + 1 :])


def dot(a, b):
    return sum(c * b.get(k, 0) for k, c in a.items())


def difference(a, b):
    result = dict(a)
    for key, value in b.items():
        result[key] = result.get(key, 0) - value
    return {k: v for k, v in result.items() if v}


def chain(terms):
    # kertr[d]: successive right rotations of(1,-1,0,...,0), d-1 rows.
    return [difference(a, b) for a, b in zip(terms[:-1], terms[1:], strict=True)]


def determinant(matrix):
    a = [[F(x) for x in row] for row in matrix]
    result = F(1)
    for i in range(len(a)):
        pivot = next((j for j in range(i, len(a)) if a[j][i]), None)
        if pivot is None:
            return F(0)
        if pivot != i:
            a[i], a[pivot] = a[pivot], a[i]
            result = -result
        value = a[i][i]
        result *= value
        for j in range(i + 1, len(a)):
            ratio = a[j][i] / value
            for k in range(i + 1, len(a)):
                a[j][k] -= ratio * a[i][k]
            a[j][i] = 0
    return result


def multiply(a, b):
    return [
        [sum(x * y for x, y in zip(row, column, strict=True)) for column in zip(*b, strict=True)]
        for row in a
    ]


def main():
    universe = tuple(range(1, 9))
    blocks = []
    for blade in combinations(range(1, 8), 4):
        complement = tuple(i for i in universe if i not in blade)
        blocks.append(
            ("L4p", [{("w", blade): F(1, 2), ("w", complement): F(sign(blade + complement), 2)}])
        )
    for blade in combinations(universe, 4):
        terms = [
            {("T", (i,), tuple(j for j in blade if j != i)): F((-1) ** k)}
            for k, i in enumerate(blade)
        ]
        blocks.append(("Y3_shift", chain(terms)))
    for blade in combinations(universe, 2):
        terms = [
            {("T", (i,), tuple(sorted((i,) + blade))): F(sign((i,) + blade))}
            for i in universe
            if i not in blade
        ]
        blocks.append(("Y3_raise", chain(terms)))
    for blade in combinations(universe, 2):
        blocks.append(("L2", [{("w", blade): F(1)}]))
    for i, j in combinations(universe, 2):
        blocks.append(("Y1_symmetric", [{("T", (i,), (j,)): F(1), ("T", (j,), (i,)): F(1)}]))
    blocks.append(("Y1_tracefree", chain([{("T", (i,), (i,)): F(1)} for i in universe])))
    dimensions = {}
    factors = {}
    owners = {}
    vectors = []
    for block_index, (kind, basis) in enumerate(blocks):
        dimensions[kind] = dimensions.get(kind, 0) + len(basis)
        gram = [[dot(a, b) for b in basis] for a in basis]
        block_det = determinant(gram)
        assert block_det > 0
        factors[kind] = factors.get(kind, F(1)) * block_det
        support = {key for v in basis for key in v}
        for key in support:
            assert key not in owners  # exact orthogonality between declared blocks
            owners[key] = block_index
        vectors.extend(basis)
    assert len(vectors) == 448
    assert dimensions == {
        "L4p": 35,
        "Y3_shift": 210,
        "Y3_raise": 140,
        "L2": 28,
        "Y1_symmetric": 28,
        "Y1_tracefree": 7,
    }
    expected = {
        "L4p": F(1, 2**35),
        "Y3_shift": F(4**70),
        "Y3_raise": F(6**28),
        "L2": F(1),
        "Y1_symmetric": F(2**28),
        "Y1_tracefree": F(8),
    }
    assert factors == expected
    target_gram_determinant = prod(factors.values())
    assert target_gram_determinant == 2**164 * 3**28

    # Metamorphic target-basis change: pairing matrix scales once, Gram twice.
    gram3 = [[F(2), F(-1), F(0)], [F(-1), F(2), F(-1)], [F(0), F(-1), F(2)]]
    diagonal = [[F(2), 0, 0], [0, F(1), 0], [0, 0, F(1)]]
    inverse = [[F(1, 2), 0, 0], [0, F(1), 0], [0, 0, F(1)]]
    transformed_gram = multiply(multiply(diagonal, gram3), diagonal)
    transformed_coordinates = inverse
    transformed_pairing = multiply(transformed_coordinates, transformed_gram)
    assert determinant(gram3) == 4
    assert determinant(transformed_gram) == 16
    assert determinant(transformed_pairing) == 8
    assert transformed_pairing == multiply(gram3, diagonal)

    fixture_path = Path(
        "/Users/mike/Dev/ctrl-research-notebook/research-notebook/publication/gu-source-exploration-20261018/software/thesis-appendix/determinant-fixtures.json"
    )
    fixtures = json.loads(fixture_path.read_text())["fixtures"]
    primes = [2, 3, 5, 7, 11, 29, 97, 101, 103]
    fingerprints = []
    for fixture in fixtures:
        value = fixture["determinant_sign"] * prod(
            int(p) ** e for p, e in fixture["prime_factorization_abs"].items()
        )
        fingerprints.append(
            {
                "label": fixture["label"],
                "source_reported_only": True,
                "modular_residues": {str(p): value % p for p in primes},
                "coordinate_valuation_after_pairing_and_double_removal": {
                    "2": fixture["prime_factorization_abs"].get("2", 0) - 612,
                    "3": fixture["prime_factorization_abs"].get("3", 0) - 28,
                }
                if value
                else None,
            }
        )
    assert all(f["modular_residues"]["2"] == 0 for f in fingerprints)
    assert all(f["modular_residues"]["97"] != 0 for f in fingerprints[:-1])
    modulus = 97 * 101 * 103
    assert all(1 % p == (1 + modulus) % p for p in (97, 101, 103))
    diagnosis_primes = (97, 101, 103)
    normalization_syndromes = {
        "odd_one_sided_permutation": [(-1) % p for p in diagnosis_primes],
        "missing_target_gram": [
            pow((pow(2, 164, p) * pow(3, 28, p)) % p, -1, p) for p in diagnosis_primes
        ],
        "missing_matrix_double": [pow(pow(2, 448, p), -1, p) for p in diagnosis_primes],
    }
    assert (
        normalization_syndromes["odd_one_sided_permutation"][0]
        == normalization_syndromes["missing_target_gram"][0]
    )
    assert (
        normalization_syndromes["odd_one_sided_permutation"][1]
        != normalization_syndromes["missing_target_gram"][1]
    )
    assert len({tuple(v) for v in normalization_syndromes.values()}) == 3
    result = {
        "scope": "Source-target-basis Gram reconstruction only; no symbol matrix, projected operators, or fixture determinant computed.",
        "dimensions": dimensions,
        "block_gram_determinants": factors,
        "target_gram_factorization": {"2": 164, "3": 28},
        "printed_pairing_double_to_coordinate_factorization": {"2": 612, "3": 28},
        "basis_normalization_metamorphic": {
            "original_gram_det": 4,
            "rescaled_gram_det": 16,
            "rescaled_pairing_det_same_map": 8,
        },
        "source_fixture_fingerprints": fingerprints,
        "finite_prime_collision_negative": {"integers": [1, 1 + modulus], "primes": [97, 101, 103]},
        "conditional_normalization_diagnosis": {
            "primes": diagnosis_primes,
            "observed_to_expected_ratios": normalization_syndromes,
            "caveat": "Finite list of modeled mistakes only; not a complete fault classifier or equality proof.",
        },
        "source_derived_coefficient_scaling_contract": {
            "L3_injection_pair_degree": 56,
            "L4p_projection_triple_degree": 35,
            "Y3_projection_pair_degree": 350,
            "L2_projection_triple_degree": 28,
            "all_ten_scaled_degree": 469,
            "status": "Predicted from source dependency and dimension structure; not tested against an assembled symbol matrix.",
        },
        "ordering_scope": "Within-block ordering of signed orthogonal terms cannot change these Gram determinants. Matching final source row/column ordering and signs remains a separate obligation.",
    }
    output = json.dumps(result, default=str, indent=2)
    Path(__file__).with_suffix(".json").write_text(output + "\n")
    print(output)


if __name__ == "__main__":
    main()
