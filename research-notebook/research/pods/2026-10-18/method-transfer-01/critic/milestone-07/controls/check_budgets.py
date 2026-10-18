"""Independent exact face and clock arithmetic; no trajectory simulation."""
from fractions import Fraction as F
from itertools import product
import json

target, drift, radius, delay = F(9,200), F(3,1700), F(2221,40000), F(1,2000)
weights = [F(51,50),F(101,100),F(1)]
residual = F(111,1000)
rows = []
for r in [F(8), F(12)]:
    matrix = [[F(-4),F(4),F(0)], [F(0),F(-4),F(4)],
              [4*(1-r/8),12*(r/8-1),4*(2-3*r/8)]]
    for i in range(3):
        # Positive face; the negative face follows by simultaneous sign reversal.
        a = matrix[i][i]*weights[i]+sum(abs(matrix[i][j])*weights[j] for j in range(3) if j!=i)
        b = r*residual/16 if i==2 else F(0)
        assert a < 0
        margin = -weights[i]*drift-(a*target+b)
        assert margin >= 0
        rows.append({'rate':str(r),'face':i,'slope_in_K':str(a),
                     'constant':str(b),'minimum_inward_margin':str(margin)})
# For fixed z,w,K the face expression is affine in r; endpoint bounds cover [8,12].
outward_at_12_wide = F(-19,10)*target + F(12,16)*F(3,25)
outward_at_16 = F(1,5)*target+residual
assert outward_at_12_wide==F(9,2000) and outward_at_16==F(3,25)
entry = (radius-target)/drift
assert entry==F(7157,1200)
gap_without_delay=drift*delay
center=F(7,50)-F(1,100)/4-F(117,100)/32
assert center==F(323,3200)
assert center+radius>F(3,20) and center+weights[0]*target<F(3,20)
print(json.dumps({'passed':True,'face_checks':rows,
 'all_radius_argument':'Each corner maximum decreases in K; evaluate at target. Each fixed-state expression is affine in r, so endpoints suffice.',
 'wide_residual_outward':str(outward_at_12_wide),'floor_only_outward':str(outward_at_16),
 'entry_time':str(entry),'delayed_deadline':str(entry+delay),'missing_delay_envelope_gap':str(gap_without_delay),
 'nominal_center':str(center),'whole_time_upper_tube':str(center+radius),
 'late_upper_tube':str(center+weights[0]*target),
 'scope':'Exact aggregate face and envelope arithmetic, not physical unsafe sampled trajectories.'},indent=2))
