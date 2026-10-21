"""Exact fixed-word design diagnostics; no hardware ADC or compiler theorem claimed."""

import json
from fractions import Fraction as F
from pathlib import Path


def nearest_even(x):
    q, r = divmod(x.numerator, x.denominator)
    if 2 * r < x.denominator:
        return q
    if 2 * r > x.denominator:
        return q + 1
    return q + (q % 2)


def energy(x, v):
    return 5 * x * x + 2 * x * v + v * v


def clip(n, bound):
    return max(-bound, min(bound, n))


def wrap16(n):
    return (n + 32768) % 65536 - 32768


for x in [F(1, 2), F(3, 2), F(-1, 2), F(-3, 2), F(7, 3), F(-7, 3)]:
    assert abs(nearest_even(x) - x) <= F(1, 2)
# E<=.1 implies |x|<.159, |v|<.354 from completed squares.
# These rounded-out integer boxes deliberately exceed the sharp state projection.
formats = []
for frac, xc, vc in [(14, 2606, 5801), (16, 10421, 23201)]:
    scale = 2**frac
    assert F(159, 1000) * scale + F(1, 2) <= xc
    assert F(177, 500) * scale + F(1, 2) <= vc
    dot_bound = 2 * xc + 3 * vc
    input_error = F(5, 2 * scale)
    assert input_error <= F(1, 4000)
    assert dot_bound < 2**31
    formats.append(
        {
            "fraction_bits": frac,
            "scale": scale,
            "x_count_bound": xc,
            "v_count_bound": vc,
            "dot_count_bound": dot_bound,
            "int16_inputs_fit": max(xc, vc) < 32768,
            "int16_dot_bound_fits": dot_bound < 32768,
            "output_limit_count": scale,
            "weighted_quantization_error": input_error,
            "remaining_controller_error_budget": F(1, 4000) - input_error,
        }
    )
assert formats[0]["int16_dot_bound_fits"] and not formats[1]["int16_dot_bound_fits"]
x, v = F(-1, 20), F(7, 20)
assert energy(x, v) == F(1, 10)
nominal = -2 * x - 3 * v
assert nominal == F(-19, 20)
scale = 2**16
X, V = nearest_even(scale * x), nearest_even(scale * v)
assert X == -3277 and V == 22938
correct = clip(-2 * X - 3 * V, scale)
wrong = clip(-2 * X - wrap16(3 * V), scale)
assert correct == -62260 and wrong == 3276
assert abs(F(correct, scale) - nominal) <= F(5, 2 * scale)
assert F(wrong - correct, scale) == 1
# Per-term clamps violate the source clamp-after-dot operation even without machine overflow.
termwise = max(F(-1), min(F(1), -2 * x)) + max(F(-1), min(F(1), -3 * v))
assert termwise == F(-9, 10)
assert abs(termwise - nominal) == F(1, 20) > F(1, 4000)
# Unexpected noise-shaping negative: zero sum of held error does not cancel closed-loop state.
eps, h = F(1, 4000), F(1, 2)
sx = sv = F(0)
trace = []
for error in [eps, -eps]:
    u = -2 * sx - 3 * sv + error
    assert abs(u) <= 1
    sx, sv = sx + h * sv + h * h * u / 2, sv + h * u
    trace.append({"command_error": error, "delivered_u": u, "x": sx, "v": sv})
assert sx == eps / 32 and sv == -7 * eps / 8
# Strict-interior witness also passes a four-corner quantization-cell energy guard.
xi, vi = F(-1, 20), F(349, 1000)
Xi, Vi = nearest_even(scale * xi), nearest_even(scale * vi)
cell_energy = [
    energy(F(2 * Xi + sx, 2 * scale), F(2 * Vi + sv, 2 * scale)) for sx in [-1, 1] for sv in [-1, 1]
]
assert max(cell_energy) < F(1, 10)
ci, wi = clip(-2 * Xi - 3 * Vi, scale), clip(-2 * Xi - wrap16(3 * Vi), scale)
assert (Xi, Vi, ci, wi) == (-3277, 22872, -62062, 3474)
assert F(wi - ci, scale) == 1
result = {
    "formats": formats,
    "interior_cell_negative": {
        "X": Xi,
        "V": Vi,
        "four_corner_energies": cell_energy,
        "correct_count": ci,
        "wrapped_count": wi,
        "error": 1,
    },
    "rounding": "nearest, ties to even, exact rational executable model",
    "invariant_boundary": {"x": x, "v": v, "energy": energy(x, v)},
    "Q16_negative": {
        "X": X,
        "V": V,
        "three_V": 3 * V,
        "wrap16_three_V": wrap16(3 * V),
        "correct_output_count": correct,
        "wrong_output_count": wrong,
        "wrong_output": F(wrong, scale),
        "error_vs_correct": 1,
        "semantics": "Explicit modulo16 simulation; not a claim about C signed overflow, integer promotion, or actual deployed code.",
    },
    "clamp_order_negative": {
        "source_clamp_after_dot": nominal,
        "termwise_clamp_then_sum": termwise,
        "error": abs(termwise - nominal),
    },
    "zero_sum_error_diagnostic": trace,
    "limits": [
        "Q14/Q16 are declared alternative formats, not exact implementations of decimal delta1/10000.",
        "Input quantizer error is assumed bounded or checked against a cell; no ADC/firmware correspondence is proved.",
        "Q16 needs int32 accumulator and output; bounded int16 input codes alone are insufficient.",
        "Error-shaping diagnostic uses allowed held command errors, not a claimed output of nearest quantization.",
    ],
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, default=str, indent=2) + "\n")
print(
    {
        "formats": [
            (r["fraction_bits"], r["dot_count_bound"], str(r["weighted_quantization_error"]))
            for r in formats
        ],
        "Q16_wrong_sign": str(F(wrong, scale)),
        "clamp_order_error": str(abs(termwise - nominal)),
        "zero_sum_errors_final_state": [str(sx), str(sv)],
    }
)
