"""Independent compiled replay and exact integer checker, valid int16 input domain."""

import hashlib
import json
import random
import subprocess
from pathlib import Path

P = Path(__file__).resolve().parent
src = P / "pm_decimal.c"
snapshot = P / "critic_decimal.c"
snapshot.write_bytes(src.read_bytes())
cc = subprocess.run(
    [
        "clang",
        "-std=c11",
        "-O1",
        "-Wall",
        "-Wextra",
        "-Werror",
        "-fsanitize=undefined,signed-integer-overflow",
        "-fno-sanitize-recover=all",
        str(snapshot),
        "-o",
        str(P / "critic_decimal"),
    ],
    capture_output=True,
    text=True,
)
(P / "critic_cc.log").write_text(cc.stdout + cc.stderr)
assert cc.returncode == 0
rng = random.Random(3303)
pts = [
    (x, v)
    for x in [-32768, -1601, -500, 0, 500, 1601, 32767]
    for v in [-32768, -3601, -3500, 0, 3500, 3601, 32767]
]
pts += [(rng.randrange(-32768, 32768), rng.randrange(-32768, 32768)) for _ in range(2048)]
run = subprocess.run(
    [str(P / "critic_decimal")],
    input="".join(f"{x} {v}\n" for x, v in pts),
    capture_output=True,
    text=True,
)
assert run.returncode == 0 and not run.stderr
rows = run.stdout.splitlines()
assert len(rows) == len(pts)


def E(x, v):
    return 4 * x * x + (x + v) ** 2


bad_wrap = []
for (x, v), line in zip(pts, rows, strict=True):
    a = list(map(int, line.split()))
    q = max(E(2 * x + s, 2 * v + t) for s in [-1, 1] for t in [-1, 1])
    u = -2 * x - 3 * v
    wrap = (q + 2**31) % 2**32 - 2**31
    assert a == [
        x,
        v,
        u,
        max(-10000, min(10000, u)),
        int(E(x, v) <= 10000000),
        int(q <= 40000000),
        q,
        int(wrap <= 40000000),
    ]
    if q > 40000000 and wrap <= 40000000:
        bad_wrap.append({"x": x, "v": v, "quad": q, "int32_wrap": wrap})
assert bad_wrap
sweep = subprocess.run([str(P / "critic_decimal"), "--sweep"], capture_output=True, text=True)
assert sweep.returncode == 0 and not sweep.stderr
result = {
    "source_sha256": hashlib.sha256(src.read_bytes()).hexdigest(),
    "snapshot_sha256": hashlib.sha256(snapshot.read_bytes()).hexdigest(),
    "compiler": subprocess.check_output(["clang", "--version"], text=True).splitlines()[0],
    "cases": len(pts),
    "finite_sweep": json.loads(sweep.stdout),
    "false_int32_energy_examples": bad_wrap[:5],
    "scope": "Fresh UBSan local compilation plus exact Python arithmetic comparison on declared valid int16 codes. No compiler-refinement theorem or physical ADC claim. scanf out-of-int32 text is outside the tested input contract.",
}
(P / "critic_c_replay.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result))
