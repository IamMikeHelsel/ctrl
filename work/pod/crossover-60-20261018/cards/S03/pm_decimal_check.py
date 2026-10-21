"""Independent Python integer oracle for the compiled C arithmetic experiment."""

import hashlib
import json
import math
import random
import subprocess
from pathlib import Path

P = Path(__file__).resolve().parent
cases = set()
for x in range(-1582, 1583):
    b = 10000000 - 4 * x * x
    if b >= 0:
        k = math.isqrt(b)
        for v in [-x - k, -x + k]:
            for d in range(-2, 3):
                cases.add((x, v + d))
for x in [-32768, -30000, -1600, 0, 1600, 30000, 32767]:
    for v in [-32768, -30000, -3600, 0, 3600, 30000, 32767]:
        cases.add((x, v))
rng = random.Random(103)
for _ in range(5000):
    cases.add((rng.randrange(-32768, 32768), rng.randrange(-32768, 32768)))
cases = sorted(cases)
data = "".join(f"{x} {v}\n" for x, v in cases)
r = subprocess.run([str(P / "pm_decimal")], input=data, text=True, capture_output=True, check=True)
lines = r.stdout.splitlines()
assert len(lines) == len(cases)
wrong32 = []
point_only = []
for (x, v), line in zip(cases, lines, strict=True):
    xx, vv, u, clipped, point, safe, q, bad = map(int, line.split())
    assert (x, v) == (xx, vv)
    expected = max(
        5 * (2 * x + sx) ** 2 + 2 * (2 * x + sx) * (2 * v + sv) + (2 * v + sv) ** 2
        for sx in [-1, 1]
        for sv in [-1, 1]
    )
    assert u == -2 * x - 3 * v and clipped == max(-10000, min(10000, u))
    assert q == expected and bool(safe) == (q <= 40000000)
    assert bool(point) == (5 * x * x + 2 * x * v + v * v <= 10000000)
    if bad and not safe:
        wrong32.append([x, v, q])
    if point and not safe:
        point_only.append([x, v, q])
assert wrong32 and point_only
out = {
    "tested": len(cases),
    "boundary_false_point_accepts": len(point_only),
    "explicit_wrapped32_false_accepts": len(wrong32),
    "first_point_only": point_only[:3],
    "first_wrong32": wrong32[:3],
    "compiler": subprocess.run(
        ["clang", "--version"], capture_output=True, text=True, check=True
    ).stdout.splitlines()[0],
    "source_sha256": hashlib.sha256((P / "pm_decimal.c").read_bytes()).hexdigest(),
    "binary_sha256": hashlib.sha256((P / "pm_decimal").read_bytes()).hexdigest(),
    "scope": "Fresh local C execution plus Python integer oracle; no verified compilation, ADC/DAC or hardware binding. Cellguard for initialization, not a safe rejection policy.",
}
(P / "pm_decimal_check.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out))
