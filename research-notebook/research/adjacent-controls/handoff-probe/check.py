#!/usr/bin/env python3
"""Exact-rational interval diagnostic for a brake-to-terminal-set candidate.

This is NOT a Lean proof. The accompanying README lists analytic obligations.
No floating point or numerical ODE integration is used in acceptance checks.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import json

class I:
    def __init__(self, lo, hi=None):
        self.lo, self.hi = F(lo), F(lo if hi is None else hi)
        assert self.lo <= self.hi
    def __add__(self, y):
        y = lift(y)
        return I(self.lo+y.lo, self.hi+y.hi)
    __radd__ = __add__
    def __neg__(self): return I(-self.hi, -self.lo)
    def __sub__(self, y): return self+-lift(y)
    def __rsub__(self, y): return lift(y)+-self
    def __mul__(self, y):
        y = lift(y)
        z = [a*b for a in (self.lo,self.hi) for b in (y.lo,y.hi)]
        return I(min(z), max(z))
    __rmul__ = __mul__
    def __truediv__(self, y):
        y=lift(y)
        assert y.lo>0
        return self*I(1/y.hi, 1/y.lo)
    def sq(self):
        return I(0 if self.lo<=0<=self.hi else min(self.lo**2,self.hi**2), max(self.lo**2,self.hi**2))

def lift(x): return x if isinstance(x,I) else I(x)

def exp_minus_point(x):
    # Taylor remainder for exp(-x): degree16 upper, degree17 lower for x>=0.
    assert x>=0
    term=total=F(1)
    for k in range(1,17):
        term *= -x/k
        total += term
    return I(total+term*(-x)/17, total)

def exp_minus(x):
    assert x.lo>=0
    return I(exp_minus_point(x.hi).lo, exp_minus_point(x.lo).hi)

P=[[F(38,5),F(257,25),F(5)],
   [F(257,25),F(1319,50),F(769,50)],
   [F(5),F(769,50),F(278,25)]]

def energy(z):
    return sum((P[i][i]*z[i].sq() for i in range(3)),I(0)) + sum(
        (2*P[i][j]*z[i]*z[j] for i in range(3) for j in range(i+1,3)),I(0))

def terminal(r,z,T):
    x,v,a=map(lift,z)
    e=exp_minus(r*T)
    return [x+v*T-T*T/2+(a+1)/r*(T-(1-e)/r),
            v-T+(a+1)*(1-e)/r,
            -1+(a+1)*e]

T=F(5,4)
box=[I(F(99,100),F(101,100)), I(F(49,100),F(51,100)), I(F(-1,100),F(1,100))]
initial_energy=energy(box)
assert initial_energy.lo>12
# During u=-1, acceleration stays between -1 and a0<=.01.
# Integrating gives position lower >=.99+.49t-t²/2 and upper <=1.01+.51t+.01t²/2.
# Concavity of the lower polynomial and monotonicity of the upper on[0,T]
# yield the endpoint bounds below. These analytic steps are not formalized here.
position_lower=min(box[0].lo, box[0].lo+box[1].lo*T-T*T/2)
position_upper=box[0].hi+box[1].hi*T+box[2].hi*T*T/2
assert -2<position_lower and position_upper<2
corners=list(product(*[(v.lo,v.hi) for v in box]))
records=[]
for n in range(80):
    r=I(F(9,10)+F(n,400),F(9,10)+F(n+1,400))
    for c in corners:
        b=energy(terminal(r,c,T))
        assert b.hi<12,(n,c,b.hi)
        records.append(b.hi)
# For each fixed r, terminal flow is affine in the initial state and P is PSD.
# Convexity then bounds every point in the box by its maximum vertex energy.
maximum=max(records)
root=Path(__file__).resolve().parents[3]
source=root/'lean-controls/LeanControls/Generated/TravelQuarterLower.lean'
out={
    'status':'exact-rational diagnostic passed; analytic composition not Lean-checked',
    'model':'x_prime=v; v_prime=a; a_prime=r*(-1-a), fixed r in[9/10,11/10], no disturbances during backup',
    'initial_box':[[str(v.lo),str(v.hi)]for v in box],
    'hold_duration':str(T),
    'initial_energy_lower':str(initial_energy.lo),
    'position_bounds_entire_hold':[str(position_lower),str(position_upper)],
    'terminal_energy_upper_exact':str(maximum),
    'terminal_energy_upper_display':float(maximum),
    'terminal_margin_exact':str(F(12)-maximum),
    'interval_cells':80,'initial_vertices':8,'checks':len(records),
    'arithmetic':'Python Fraction; rational Taylor degree16/17 bounds; no floating-point acceptance',
    'frozen_P_source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
    'assumptions_to_formalize':['held flow matches ODE','Taylor exp bounds','P PSD and convex vertex maximum','whole-segment acceleration/position comparison','terminal-state and time-shift composition with original controller'],
    'not_claimed':['Lean proof','hardware validity','optimal recovery region','nonzero backup disturbance robustness','novel stopping formula','fully implemented runtime shield'],
}
Path(__file__).with_name('results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k]for k in ['status','initial_energy_lower','position_bounds_entire_hold','terminal_energy_upper_display','checks']}))
