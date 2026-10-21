"""Exact, fixed-correspondence SO(3), known-scale support and active-query fixtures."""

import json
from fractions import Fraction as F
from itertools import combinations, permutations, product
from pathlib import Path


def vec(*xs):
    return tuple(F(x) for x in xs)


def add(a, b):
    return tuple(x + y for x, y in zip(a, b, strict=True))


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b, strict=True))


def scale(s, a):
    return tuple(s * x for x in a)


def dot(a, b):
    return sum(x * y for x, y in zip(a, b, strict=True))


def cross(a, b):
    return (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0])


def determinant(columns):
    return dot(columns[0], cross(columns[1], columns[2]))


def apply_rotation(columns, x):
    return tuple(sum(columns[j][i] * x[j] for j in range(3)) for i in range(3))


def noncollinear(points, ids):
    a, b, c = (points[i] for i in ids)
    return dot(cross(sub(b, a), sub(c, a)), cross(sub(b, a), sub(c, a))) != 0


def fit_triple(points, targets, ids):
    """Every proper rigid fit of this noncollinear labeled triangle is this unique map."""
    a, b, c = (points[i] for i in ids)
    aa, bb, cc = (targets[i] for i in ids)
    u, v = sub(b, a), sub(c, a)
    uu, vv = sub(bb, aa), sub(cc, aa)
    if (dot(u, u), dot(v, v), dot(u, v)) != (dot(uu, uu), dot(vv, vv), dot(uu, vv)):
        return None
    w, ww = cross(u, v), cross(uu, vv)
    det = determinant((u, v, w))
    if det == 0:
        return None

    def rotate(x):
        coordinates = (dot(x, cross(v, w)) / det, dot(x, cross(w, u)) / det, dot(x, w) / det)
        return add(
            add(scale(coordinates[0], uu), scale(coordinates[1], vv)), scale(coordinates[2], ww)
        )

    columns = tuple(rotate(vec(*(int(i == j) for i in range(3)))) for j in range(3))
    assert determinant(columns) == 1
    assert all(dot(columns[i], columns[j]) == int(i == j) for i in range(3) for j in range(3))
    translation = sub(aa, rotate(a))
    return columns, translation


def enumerate_fits(points, targets, minimum_support):
    candidates = {}
    for ids in combinations(range(len(points)), 3):
        fit = fit_triple(points, targets, ids)
        if fit is None:
            continue
        rotation, translation = fit
        support = tuple(
            i
            for i, p in enumerate(points)
            if add(apply_rotation(rotation, p), translation) == targets[i]
        )
        if len(support) >= minimum_support:
            candidates[fit] = support
    return candidates


def serialize_fits(fits):
    return [{"rotation_columns": r, "translation": t, "support": s} for (r, t), s in fits.items()]


def main():
    points = [vec(0, 0, 0), vec(1, 0, 0), vec(0, 1, 0), vec(0, 0, 1)]
    targets = points[:3] + [vec(0, 0, -1)]
    assert all(noncollinear(points, ids) for ids in combinations(range(4), 3))
    fits4 = enumerate_fits(points, targets, 3)
    # The first prediction of exactly two was falsified: reflected tetrahedron has four.
    assert len(fits4) == 4
    assert sorted(fits4.values()) == list(combinations(range(4), 3))

    off_axis = vec(0, 2, 1)
    points5, targets5 = points + [off_axis], targets + [off_axis]
    assert all(noncollinear(points5, ids) for ids in combinations(range(5), 3))
    fits5 = enumerate_fits(points5, targets5, 4)
    assert len(fits5) == 1
    assert next(iter(fits5.values())) == (0, 1, 2, 4)

    on_axis = vec(2, 0, 0)
    on_axis_fits = enumerate_fits(points + [on_axis], targets + [on_axis], 4)
    assert len(on_axis_fits) == 2
    assert sorted(on_axis_fits.values()) == [(0, 1, 2, 4), (0, 1, 3, 4)]

    # n=5, f=1 meets the raw count threshold, but a collinear overlap defeats uniqueness.
    assert not noncollinear(points + [on_axis], (0, 1, 4))
    eps = F(1, 100)
    near_points = [vec(0, 0, 0), vec(1, 0, 0), vec(2, eps, 0)]
    near_targets = [vec(0, 0, 0), vec(1, 0, 0), vec(2, 0, 0)]
    identity = (vec(1, 0, 0), vec(0, 1, 0), vec(0, 0, 1))
    flip = (vec(1, 0, 0), vec(0, -1, 0), vec(0, 0, -1))
    near_errors = [
        [
            dot(sub(apply_rotation(r, p), y), sub(apply_rotation(r, p), y))
            for p, y in zip(near_points, near_targets, strict=True)
        ]
        for r in (identity, flip)
    ]
    assert noncollinear(near_points, (0, 1, 2))
    assert all(e <= eps**2 for errors in near_errors for e in errors)
    rotation_distance_squared = sum(
        dot(sub(identity[i], flip[i]), sub(identity[i], flip[i])) for i in range(3)
    )
    assert rotation_distance_squared == 8

    # Exact two-hypothesis discrimination threshold for Euclidean bounded query noise.
    query = vec(0, eps, 0)
    qa, qb = apply_rotation(identity, query), apply_rotation(flip, query)
    midpoint = scale(F(1, 2), add(qa, qb))
    separation_squared = dot(sub(qa, qb), sub(qa, qb))
    assert separation_squared == 4 * eps**2
    assert dot(sub(qa, midpoint), sub(qa, midpoint)) == eps**2
    assert dot(sub(qb, midpoint), sub(qb, midpoint)) == eps**2

    # Relaxing SO(3) to O(3) defeats the five-pair uniqueness conclusion.
    reflection = (vec(1, 0, 0), vec(0, 1, 0), vec(0, 0, -1))
    reflection_support = [
        i for i, p in enumerate(points5) if apply_rotation(reflection, p) == targets5[i]
    ]
    assert determinant(reflection) == -1 and reflection_support == [0, 1, 2, 3]

    # Unknown correspondence search is a different problem, even without outliers.
    tetra = [vec(1, 1, 1), vec(1, -1, -1), vec(-1, 1, -1), vec(-1, -1, 1)]
    fixed_tetra = enumerate_fits(tetra, tetra, 4)
    unordered_tetra = {}
    for perm in permutations(range(4)):
        for fit, support in enumerate_fits(tetra, [tetra[i] for i in perm], 4).items():
            unordered_tetra[fit] = support
    assert len(fixed_tetra) == 1 and len(unordered_tetra) == 12

    # Declared finite virtual feature pool, no physical acquisition feasibility assumed.
    # Score worst prediction separation among ALL four surviving hypotheses.
    query_scores = []
    for xyz in product(range(-2, 3), repeat=3):
        candidate = vec(*xyz)
        if dot(candidate, candidate) > 5:
            continue
        predictions = [add(apply_rotation(r, candidate), t) for r, t in fits4]
        minimum_gap_squared = min(
            dot(sub(a, b), sub(a, b)) for a, b in combinations(predictions, 2)
        )
        query_scores.append((minimum_gap_squared, candidate))
    best_score = max(score for score, _ in query_scores)
    selected_score = next(score for score, candidate in query_scores if candidate == off_axis)
    assert best_score == 8 and selected_score == 4
    # Heteroscedastic extension: original four pairs exact, added query error <=1.
    # At selected point, I and the y-axis half-turn share a radius-one observation.
    identity_prediction = off_axis
    second_prediction = vec(0, 2, -1)
    ambiguous_new_observation = vec(0, 2, 0)
    assert (
        dot(
            sub(identity_prediction, ambiguous_new_observation),
            sub(identity_prediction, ambiguous_new_observation),
        )
        == 1
    )
    assert (
        dot(
            sub(second_prediction, ambiguous_new_observation),
            sub(second_prediction, ambiguous_new_observation),
        )
        == 1
    )
    # At best point all prediction pairs are farther than twice that error bound.
    # Triangle inequality then forbids a query observation admitted by two hypotheses.
    assert best_score > 4

    result = {
        "model": "fixed labeled correspondences, known scale 1, R in SO(3), absolute fault budget f=1",
        "four_pair_all_three_point_fits": serialize_fits(fits4),
        "off_axis_fifth_pair_four_point_fits": serialize_fits(fits5),
        "on_axis_fifth_pair_negative": serialize_fits(on_axis_fits),
        "noisy_near_collinear": {
            "epsilon": eps,
            "source_triangle_area_squared": eps**2 / 4,
            "squared_residuals": near_errors,
            "rotation_Frobenius_distance_squared": rotation_distance_squared,
        },
        "active_query_boundary": {
            "query": query,
            "prediction_separation_squared": separation_squared,
            "shared_midpoint": midpoint,
            "epsilon": eps,
        },
        "orientation_scope_negative": {
            "determinant": determinant(reflection),
            "reflection_support_after_off_axis_fifth": reflection_support,
        },
        "correspondence_scope_negative": {
            "fixed_labeled_full_support_poses": len(fixed_tetra),
            "unlabeled_full_support_poses": len(unordered_tetra),
        },
        "finite_virtual_query_pool": {
            "integer_coordinate_range": [-2, 2],
            "squared_radius_bound": 5,
            "count": len(query_scores),
            "all_hypothesis_minimum_gap_squared_at_selected": selected_score,
            "best_minimum_gap_squared": best_score,
            "maximizers": [candidate for score, candidate in query_scores if score == best_score],
            "new_query_error_only": 1,
            "original_four_error": 0,
            "selected_query_ambiguous_observation": ambiguous_new_observation,
            "best_query_pairwise_separation_squared_exceeds_four": best_score > 4,
        },
        "completeness": "Every candidate with required support contains a noncollinear triple in these fixtures; all triples enumerated. Support fixtures keep fixed labels. Only the separate regular-tetrahedron scope negative enumerates all24 correspondence permutations.",
    }
    output = json.dumps(result, default=str, indent=2)
    Path(__file__).with_suffix(".json").write_text(output + "\n")
    print(output)


if __name__ == "__main__":
    main()
