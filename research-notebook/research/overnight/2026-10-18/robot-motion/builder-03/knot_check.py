"""Exact reference-jerk checker for finite four-box target histories.

All input numbers are rational. The result is not a physical-jerk certificate.
Soundness for every real time is the proposed Lean theorem, not yet proved here.
"""
from fractions import Fraction as Q

def kernel_jerk(x):
    if x <= 0 or x >= 4:
        return Q(0)
    if x <= 1:
        return x
    if x <= 2:
        return 4-3*x
    if x <= 3:
        return 3*x-8
    return 4-x

def step_response(x):
    if x <= 0:
        return Q(0)
    if x >= 4:
        return Q(1)
    return sum(Q(c,24)*max(x-i,Q(0))**4 for i,c in enumerate([1,-4,6,-4,1]))

def reference_jerk(events, h, t):
    return sum(delta*kernel_jerk((t-tau)/h)/h**3 for tau,delta in events)

def reference_position(events, h, t, initial=Q(0)):
    return initial+sum(delta*step_response((t-tau)/h) for tau,delta in events)

def remaining_check(events, h, limit, now):
    assert h > 0 and limit >= 0
    # now is essential when it is inside an affine interval.
    knots = sorted({now} | {tau+m*h for tau,_ in events for m in range(5) if tau+m*h >= now})
    rows = [(t,reference_jerk(events,h,t)) for t in knots]
    peak_t,peak = max(rows,key=lambda item:abs(item[1]))
    return {"passed": abs(peak)<=limit, "peak_abs": abs(peak), "peak_signed": peak, "peak_time": peak_t, "knots": rows}

def local_variation(events,h,t):
    return sum(abs(delta) for tau,delta in events if t-4*h <= tau <= t)

def maximum_local_variation(events,h):
    # The closed-window total can increase only when an event enters.
    return max((local_variation(events,h,tau) for tau,_ in events),default=Q(0))
