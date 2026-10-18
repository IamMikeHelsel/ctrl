#!/usr/bin/env python3
from pathlib import Path
from fractions import Fraction as F
import json,math
x=F(1,1000);v=F(41,100);A=F(1,10);T=F(1,20);b=F(6,5);k=F(8)
P=x+v*T+A*T*T/2;U=v+A*T;C=(A+b)/k
quad=lambda s:P+(U+C)*s-b*s*s/2
bounds=[quad(F(1,5)),quad(F(31,100))-C/k*(1-F(21,100)),P+(U+C)**2/(2*b)-C/k*(1-F(21,250))]
assert all(z<F(71,500) for z in bounds)
series=sum((F(62,25)**n/F(math.factorial(n)) for n in range(11)),F(0));assert series>F(250,21)
terminal=U-b*F(479,1000)+C*(1-F(256,14641));assert terminal<0
base_peak=quad(F(12,25))-C/k;assert base_peak>F(7,50)
assert P==F(173,8000) and U==F(83,200)
endpoint_pos_upper=quad(F(1));endpoint_vel_upper=U-b+C
assert endpoint_pos_upper<0 and endpoint_vel_upper<0
out={'passed':True,'engagement_position':str(P),'engagement_velocity':str(U),
 'three_interval_position_upper':[str(z) for z in bounds],
 'late_bound_margin':str(F(71,500)-bounds[2]),'exp_Taylor_lower':str(series),
 'terminal_velocity_upper_using_exp_lower':str(terminal),
 'position_at_48hundredths_strict_lower':str(base_peak),
 'endpoint_only_trap':{'endpoint_position_upper':str(endpoint_pos_upper),'endpoint_velocity_upper':str(endpoint_vel_upper),'earlier_position_strict_lower':str(base_peak)}}
Path(__file__).with_name('independent-arithmetic.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
