"""Independent decimal diagnostic of full retained three-state ramp and inner residual."""

import json
from decimal import Decimal as D
from decimal import localcontext
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
with localcontext() as ctx:
    ctx.prec = 90
    receipt = json.loads((HERE / "critic_perturbed.json").read_text())
    xs = [D(".0001")] * 3
    es = [D(0)] * 3
    decay = D("-.8").exp()
    peak = D(0)
    accmax = D(0)
    speedmax = D(0)
    checks = []
    for row in receipt["rows"]:
        f = F(row["force"])
        force = D(f.numerator) / D(f.denominator)
        old = -10 * (xs[-3] + es[-3])
        new = -10 * (xs[-2] + es[-2])
        xn = xs[-1] + (old + new) / 100
        en = force / 40 + decay * (es[-1] - force / 40)
        y = xn + en
        xs.append(xn)
        es.append(en)
        peak = max(peak, abs(y))
        accmax = max(accmax, abs(new - old) * 50)
        speedmax = max(speedmax, abs(old), abs(new))
        checks.append({"step": row["step"], "actual": str(y)})
    result = {
        "peak": str(peak),
        "acceleration": str(accmax),
        "speed": str(speedmax),
        "history_length": 3,
        "rows": checks,
        "scope": "Independent90digit numerical replay, not interval or kernel proof; correct one-sample delayed ramp indexing.",
    }
    (HERE / "pm_perturbed_replay.json").write_text(json.dumps(result, indent=2) + "\n")
    print({k: v for k, v in result.items() if k != "rows"})
