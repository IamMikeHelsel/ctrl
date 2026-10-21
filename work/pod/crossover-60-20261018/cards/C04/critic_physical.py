"""Independent DOP853 replay of root's worst sampled-position C04 fixture."""

import json
from fractions import Fraction as F
from pathlib import Path

from scipy.integrate import solve_ivp

HERE = Path(__file__).resolve().parent
producer = json.loads((HERE / "pm_physical.json").read_text())
case = max(producer["cases"], key=lambda row: row["peak_sampled_x"])
m = tuple(F(v) for v in case["reading"])
w = (F(51, 50), F(101, 100), F(1))
e = tuple(F(n, 10**8) for n in (101533, 368033, 1042283))
n = (F(1, 1000), F(1, 100), F(1, 20))
o = (m[0], m[0] + m[1] / 4, m[0] + m[1] / 2 + m[2] / 16)
K = max(
    F(9, 200), *((o[i] - o[j] + e[i] + e[j]) / (w[i] + w[j]) for i in range(3) for j in range(3))
)
c = max(o[i] + e[i] - w[i] * K for i in range(3))
assert float(c) == case["center"] and float(K) == case["policy_radius"]
state = [float(m[i] - case["initial_sensor_signs"][i] * n[i]) for i in range(3)]
mode = case["mode"]
u, rate, d = -1.21, (8 if mode == 0 else 12), (0.01 if mode == 0 else -0.01)
t = F(0)
stamp = F(0)
peak = state[0]
age = F(0)
violation = -1.0
index = 0
while t < 2:
    dispatch = F(1, 2000) + index * F(29, 2000)
    events = (
        [(dispatch, "dispatch")]
        if index == 0
        else [(dispatch - F(1, 2000), "sample"), (dispatch, "dispatch")]
    )
    for end, event in events:
        end = min(end, F(2))
        if end <= t:
            continue
        sol = solve_ivp(
            lambda _, y, rate=rate, u=u, d=d: [y[1], y[2], rate * (u + d - y[2])],
            (float(t), float(end)),
            state,
            method="DOP853",
            rtol=1e-12,
            atol=1e-14,
            dense_output=True,
        )
        assert sol.success
        for j in range(1, 21):
            tt = t + (end - t) * F(j, 20)
            ss = sol.sol(float(tt))
            peak = max(peak, float(ss[0]))
            if tt >= F(1, 2000):
                age = max(age, tt - stamp)
                z = (
                    ss[0] - float(c),
                    ss[0] - float(c) + ss[1] / 4,
                    ss[0] - float(c) + ss[1] / 2 + ss[2] / 16,
                )
                env = max(0.045, float(K) - 3 / 1700 * (float(tt) - 0.0005))
                violation = max(violation, *(abs(z[i]) - float(w[i]) * env for i in range(3)))
        state = sol.y[:, -1]
        t = end
        if t == 2:
            break
        if event == "sample":
            reading = [state[i] + float(n[i]) * (-1) ** (index + i + mode) for i in range(3)]
        else:
            if index == 0:
                reading = list(map(float, m))
            else:
                stamp = dispatch - F(1, 2000)
            raw = -16 / 3 * (reading[0] - float(c)) - 6 * reading[1] - reading[2] / 2
            u = max(-2, min(2, raw))
            rate = 8 if (index + mode) % 2 == 0 else 12
            d = 0.01 * (-1) ** (index + mode)
    index += 1
assert age == F(3, 200)
assert abs(peak - case["peak_sampled_x"]) < 1e-10
assert max(abs(float(state[i]) - case["final_state"][i]) for i in range(3)) < 1e-10
assert violation < 0
result = {
    "source_case": case,
    "independent_peak_sampled_x": peak,
    "peak_difference": peak - case["peak_sampled_x"],
    "independent_final_state": list(map(float, state)),
    "exact_max_age": str(age),
    "sampled_shrink_violation": violation,
    "scope": "Independent numerical replay of one worst sampled-position fixture, no all-time or uncertainty-universal proof.",
}
(HERE / "critic_physical.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({k: v for k, v in result.items() if k != "source_case"}, indent=2))
