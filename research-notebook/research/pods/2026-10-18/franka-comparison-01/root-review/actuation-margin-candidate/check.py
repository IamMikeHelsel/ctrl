from fractions import Fraction as Q
from pathlib import Path
import json

T, ex, eu, x0 = Q(1, 1000), Q(1, 1000000), Q(1, 10), Q(1, 100000)
phi = -(ex + T)
b = ex + T - eu
umin, umax = ex + T - x0, eu
assert 0 < T < 1 and -Q(1, 2) < b < x0
assert -1 + eu <= umin <= umax <= 1 - eu
assert x0-ex > 0
# The affine sample map preserves [b,x0]: its slope is positive,
# its lower endpoint is fixed and its upper endpoint moves inward.
step = lambda x: (1-T)*x + T*b
assert step(b) == b and b <= step(x0) <= x0
ud = ex + T - x0
ur = ud - eu
assert ud + x0 + phi == 0
assert -1 <= ur <= 1 and abs(ur-ud) <= eu
mid = x0 + (T/2)*ur
end = step(x0)
assert mid == -Q(79009, 2000000000) < 0
assert end == -Q(89009, 1000000000) < 0
assert ur + x0 + phi == -eu
# Robust local repair adds the support function of the actuator-error ball.
repaired = ud + eu
assert -1 + eu <= repaired <= 1 - eu
assert repaired - eu + x0 + phi == 0
assert x0 + T*(repaired-eu) > 0
print(json.dumps({
    "status": "exact rational candidate; independent review required",
    "sample_period": str(T), "state_error_bound": str(ex),
    "actuation_error_bound": str(eu), "initial_state": str(x0),
    "nominal_input": str(ud), "actual_input": str(ur),
    "nominal_barrier_value": "0", "actual_barrier_value": str(-eu),
    "midpoint_state": str(mid), "first_sample_state": str(end),
    "all_k_state_interval": [str(b), str(x0)],
    "all_k_nominal_input_interval": [str(umin), str(umax)],
    "local_support_repair_first_sample": str(x0+T*(repaired-eu))
},indent=2))
