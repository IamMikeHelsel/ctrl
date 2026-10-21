"""Half-grid sensitivity check for the closest command-variation comparison."""

import json
from fractions import Fraction as F

import domain_retuned as model

model.STEP = F(1, 4000)
results = [
    model.run("fine_direct", F(800), F(60), F(1, 2), F(1, 96), direct=True),
    model.run(
        "fine_quad25_nominal", F(15625, 64), F(625, 16), F(43, 32), F(1, 16), snap_gain=F(1, 1600)
    ),
]
model.HERE.joinpath("domain_gridcheck_results.json").write_text(
    json.dumps(
        {"grid_step": str(model.STEP), "status": "numerical sensitivity only", "cases": results},
        indent=2,
    )
    + "\n"
)
for row in results:
    print(
        row["name"],
        row["sampled_max_error_m"],
        row["sampled_peak_actual_jerk"],
        row["sampled_command_tv"],
    )
