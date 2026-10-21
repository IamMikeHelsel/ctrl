#!/usr/bin/env python3
"""Outward fixed-point interval check of the terminal block, using integers only.
No numpy, scipy, binary floating point, or stochastic arithmetic in this check.
All matrix entries denote closed intervals containing exact real quantities.
"""
import json
from fractions import Fraction as F
from pathlib import Path
import argparse
Q=10**24

def down(p,q): return p//q
def up(p,q): return -((-p)//q)
def const(x):
 x=F(x); return (down(x.numerator*Q,x.denominator),up(x.numerator*Q,x.denominator))
def add(a,b): return a[0]+b[0],a[1]+b[1]
def neg(a): return -a[1],-a[0]
def sub(a,b): return add(a,neg(b))
def mul(a,b):
 p=[a[0]*b[0],a[0]*b[1],a[1]*b[0],a[1]*b[1]]
 return down(min(p),Q),up(max(p),Q)
def absolute(a): return (0 if a[0]<=0<=a[1] else min(abs(a[0]),abs(a[1])),max(abs(a[0]),abs(a[1])))
def sumv(xs):
 a=const(0)
 for x in xs: a=add(a,x)
 return a
def mm(A,B): return [[sumv(mul(x,y) for x,y in zip(row,col)) for col in zip(*B)] for row in A]
def mat(xs):return [[const(x) for x in row] for row in xs]
def eye(n):return mat([[int(i==j) for j in range(n)] for i in range(n)])
def scale(A,a):return [[mul(x,a) for x in row] for row in A]
def maxv(a,b):return max(a[0],b[0]),max(a[1],b[1])
def bound_str(a):return [str(F(a[0],Q)),str(F(a[1],Q))]

def exp_negative(x):
 # For 0<x<1, terms decrease. Even truncation is upper, next odd lower.
 assert 0<x<1
 t=F(1); s=t
 for k in range(1,13):t=t*(-x)/k;s+=t
 lower=s+t*(-x)/13
 return const(lower)[0],const(s)[1]

def trans(t):
 r=F(8); E=exp_negative(r*t); one=const(1); zero=const(0)
 a=sub(one,E); ar=mul(a,const(1/r)); xr=sub(const(t/r),mul(a,const(1/r**2)))
 A=[[one,const(t),xr],[zero,one,ar],[zero,zero,E]]
 b=[[sub(const(t*t/2),xr)],[sub(const(t),ar)],[a]]
 return A,b

def make_model():
 AT,BT=trans(F(1,1000)); AD,BD=trans(F(1,2000)); AR,BR=trans(F(1,2000)); J=mm(AR,BD)
 K=[const(8),const(6),const(F(1,2))]
 A=[[sub(AT[i][j],mul(BR[i][0],K[j])) for j in range(3)]+[J[i][0]] for i in range(3)]
 A.append([neg(k) for k in K]+[const(0)])
 G=[[BR[i][0],J[i][0],BR[i][0]] for i in range(3)]+[[const(1),const(0),const(0)]]
 S=mat([[1,0,0,0],[1,F(1,4),0,0],[1,F(1,2),F(1,16),0],[F(1,3),F(1,4),F(1,48),F(1,24)]])
 Si=mat([[1,0,0,0],[-4,4,0,0],[16,-32,16,0],[8,-8,-8,24]])
 return mm(mm(S,A),Si),mm(S,G)

def check(radius=F(7,500),steps=2000):
 A,G=make_model(); P=eye(4); noise=[const(0)]*4; worst=[const(0)]*4
 nu=[const(F(93,1000)),const(F(1,100)),const(F(1,100))]; B=const(radius)
 for i in range(steps):
  phase=[add(mul(sumv(absolute(x) for x in row),B),n) for row,n in zip(P,noise)]
  worst=[maxv(a,b) for a,b in zip(worst,phase)]
  PG=mm(P,G); noise=[add(n,sumv(mul(absolute(x),w) for x,w in zip(row,nu))) for row,n in zip(PG,noise)]
  P=mm(P,A)
 endpoint=[add(mul(sumv(absolute(x) for x in row),B),n) for row,n in zip(P,noise)]
 def upper(a):return F(a[1],Q)
 w=list(map(upper,worst)); endpoint_upper=list(map(upper,endpoint))
 speed=4*(w[0]+w[1]); accel=16*(w[0]+2*w[1]+w[2]); command=8*sum(w[:3])+F(93,1000)
 rho=max(upper(sumv(absolute(x) for x in row)) for row in P)
 checks={
 'all_exact_interval_endpoints_inside_terminal_box':all(x<radius for x in endpoint_upper),
 'block_norm_strictly_below_one':rho<1,
 'phase_speed_below_one_half':speed<F(1,2),
 'phase_acceleration_below_2p01':accel<F(201,100),
 'raw_command_below_two':command<2,
 'upper_travel_with_grid_margin':F(135,1000)+w[0]+F(126,1000000)<F(3,20),
 'lower_travel_with_grid_margin':-F(3,100)-w[0]-F(126,1000000)>-F(1,20),
 'interpolation_margin_covers_speed_drift':F(126,1000000)>(F(1,2)+F(201,100)*F(1,1000))*F(1,4000),
 }
 return dict(arithmetic='integer outward interval arithmetic; quantum 10^-24; exp(-x) enclosed by Taylor terms 12 and 13',
             assumptions='r=8,T=.001,D=.0005; sensor command noise <=.093; target error constant independently on each half interval and <=.01',
             radius=str(radius),steps=steps,checks=checks,phase_box_intervals=list(map(bound_str,worst)),endpoint_box_intervals=list(map(bound_str,endpoint)),
             block_norm_upper=str(rho),speed_upper=str(speed),acceleration_upper=str(accel),command_upper=str(command),
             transformed_matrix_intervals=[[bound_str(x) for x in row] for row in A],noise_matrix_intervals=[[bound_str(x) for x in row] for row in G])

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 result=check();assert all(result['checks'].values()),result
 a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result['checks'],indent=2))
