"""Complete exterior-leg checks and normalization mutations using critic-only algebra."""

import itertools
import json
from fractions import Fraction as F
from pathlib import Path

from critic_operator import ALL, PHI1, PHI2, SIG, combine, exterior, star, tensor, wedge_bracket

P = Path(__file__).resolve().parent


def wedge_scalar(a, b):
    out = {}
    for (fa, ca), va in a.items():
        for (fb, cb), vb in b.items():
            assert ca == cb == ()
            form, s = exterior(fa, fb)
            if s:
                out[form, ()] = out.get((form, ()), F(0)) + s * va * vb
    return {k: v for k, v in out.items() if v}


def main():
    count1 = count2 = 0
    for a, b in itertools.combinations(ALL, 2):
        basis = {((a, b), ()): F(1)}
        for j in ALL:
            out = star(wedge_scalar({((j,), ()): F(1)}, star(basis)))
            expected = {}
            if j == a:
                expected[((b,), ())] = -F(SIG[a])
            if j == b:
                expected[((a,), ())] = F(SIG[b])
            assert out == expected
            count1 += 1
        for i, j in itertools.combinations(ALL, 2):
            out = star(wedge_scalar({((i, j), ()): F(1)}, star(basis)))
            expected = {((), ()): -F(SIG[a] * SIG[b])} if (i, j) == (a, b) else {}
            assert out == expected
            count2 += 1
    R = tensor({(0, 7, 0, 7): -1})
    rho = {
        ((i, j), (k, l)): SIG[k] * SIG[l] * v for (i, j, k, l), v in R.items() if i < j and k < l
    }
    first = wedge_bracket(PHI1, star(rho), -1)
    inner = star(wedge_bracket(PHI2, star(rho), 1))
    second = star(wedge_bracket(PHI1, inner, 1))
    correct = star(combine(first, second, F(1, 2)))
    doubledPhi2 = star(combine(first, second, F(1)))
    assert correct != doubledPhi2
    # They are not related by one global sign or scale: plane components vanish
    # only in the correct normalization.
    assert ((0,), (0,)) not in correct and ((0,), (0,)) in doubledPhi2

    # Reversing volume orientation negates every star. Both odd-star source
    # terms and the final output-identification star change sign, cancelling.
    def revstar(a):
        return {k: -v for k, v in star(a).items()}

    f = wedge_bracket(PHI1, revstar(rho), -1)
    q = revstar(wedge_bracket(PHI2, revstar(rho), 1))
    d = revstar(wedge_bracket(PHI1, q, 1))
    assert revstar(combine(f, d, F(1, 2))) == correct
    (P / "critic_hodge.json").write_text(
        json.dumps(
            {
                "complete_vector_form_leg_tests": count1,
                "complete_bivector_form_leg_tests": count2,
                "Phi2_factor_two_changes_relative_scalar_coefficient": True,
                "not_repairable_by_global_sign_scale": True,
                "orientation_reversal_preserves_final_identified_operator": True,
                "scope": "Complete external-form basis tests; internal Clifford identities and source product choice are separately declared. No unique author normalization inferred.",
            },
            indent=2,
        )
        + "\n"
    )
    print(count1, count2, "Hodge leg checks and normalization controls passed")


if __name__ == "__main__":
    main()
