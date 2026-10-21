"""One-parameter family: affine sampled errors, convex jerk and variation metrics."""

import json
from pathlib import Path

from inventor_screen import run


def screen(step):
    unit = 0.001
    zero = run(29 / 480, 0, False, step, True)["trace"]
    one = run(29 / 480, unit, False, step, True)["trace"]
    lo, hi = -float("inf"), float("inf")
    qa = qb = qc = 0.0
    breaks = []
    terms = []
    for z, o in zip(zero, one, strict=True):
        assert z[0] == o[0] and z[2] == o[2]
        e, es = z[1], (o[1] - z[1]) / unit
        if abs(es) > 1e-14:
            bounds = sorted([(-0.0002 - e) / es, (0.0002 - e) / es])
            lo = max(lo, bounds[0])
            hi = min(hi, bounds[1])
        else:
            assert abs(e) <= 0.0002
        h = z[2]
        for ix in [3, 4]:
            j, js = z[ix], (o[ix] - z[ix]) / unit
            qa += h * js * js / 2
            qb += h * j * js
            qc += h * j * j / 2
        for ix in [5, 6]:
            u, us = z[ix], (o[ix] - z[ix]) / unit
            terms.append((h / 2, u, us))
            if abs(us) > 1e-14:
                breaks.append((-u / us, h * abs(us) / 2))
    assert lo <= hi
    jerk_opt = max(lo, min(hi, -qb / (2 * qa)))
    breaks.sort()
    total = sum(w for _, w in breaks)
    acc = 0
    median = 0
    for b, w in breaks:
        acc += w
        if acc >= total / 2:
            median = b
            break
    tv_opt = max(lo, min(hi, median))
    result = {
        "step": step,
        "sampled_feasible_l_interval": [lo, hi],
        "jerk_quadratic_coefficients": [qa, qb, qc],
        "jerk_optimal_l": jerk_opt,
        "minimum_sampled_jerk_integral": qa * jerk_opt**2 + qb * jerk_opt + qc,
        "TV_optimal_l": tv_opt,
        "minimum_sampled_command_TV": sum(w * abs(u + tv_opt * us) for w, u, us in terms),
        "direct": run(1 / 96, 0, True, step),
        "jerk_optimizer_replay": run(29 / 480, jerk_opt, False, step),
        "TV_optimizer_replay": run(29 / 480, tv_opt, False, step),
    }
    return result


out = [screen(h) for h in [0.0002, 0.0001]]
Path(__file__).with_name("inventor_affine.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
