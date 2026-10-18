from fractions import Fraction as F
import json

lower_accel=F(-61,50)
lower_zero=F(39,100)/(-lower_accel)
assert lower_zero==F(39,122)>F(1,10)
recovery=F(1,20)
exp_argument=8*(F(1,10)-recovery)
assert exp_argument==F(2,5)
# exp(x)>=1+x for x>=0 implies exp(-2/5)<=5/7.
exp_upper=1/(1+exp_argument)
upper_accel=F(-6,5)+F(13,10)*exp_upper
assert upper_accel==F(-19,70)<F(-1,4)
gap=F(1,1000)
true_velocity_lower=lower_accel*gap
measured_velocity_abs=-true_velocity_lower+F(1,100)
measured_accel_lower=lower_accel-F(1,20)
measured_accel_upper=upper_accel+F(1,20)
measured_x_upper=F(71,500)+F(1,1000)
assert true_velocity_lower==F(-61,50000)
assert measured_velocity_abs==F(561,50000)
assert measured_accel_lower==F(-127,100)
assert measured_accel_upper==F(-31,140)<F(-1,5)
assert measured_x_upper==F(143,1000)
sample_horizon=F(529,1000)+gap
pending_horizon=sample_horizon+F(1,2000)
assert sample_horizon==F(53,100) and pending_horizon==F(1061,2000)
# A strictly increasing sample sequence can still be Zeno:
# sigma_n=(1/2000)*(1-1/(n+1)), gap_n=1/(2000(n+1)(n+2)).
# It starts at zero, all gaps <=1/4000, all samples <1/2000<39/122.
assert F(1,4000)<=gap and F(1,2000)<lower_zero
print(json.dumps({'passed':True,'lower_zero_time':str(lower_zero),
 'exp_argument':str(exp_argument),'exp_upper_from_one_plus_x':str(exp_upper),
 'true_acceleration_interval':[str(lower_accel),str(upper_accel)],
 'true_velocity_interval':[str(true_velocity_lower),'0'],
 'measured_x_upper':str(measured_x_upper),
 'measured_abs_velocity_upper':str(measured_velocity_abs),
 'measured_acceleration_interval':[str(measured_accel_lower),str(measured_accel_upper)],
 'measured_acceleration_upper_guard_margin':str(F(-1,5)-measured_accel_upper),
 'sample_horizon':str(sample_horizon),'maximum_pending_horizon':str(pending_horizon),
 'zeno_negative':'sigma_n=(1/2000)*(1-1/(n+1)); strictly increasing from zero, gaps <=1/4000, never reaches tau>=39/122',
 'scope':'Exact algebra only. Lower barrier, comparison, integration, sampling coverage and hybrid existence are proof obligations.'},indent=2))
