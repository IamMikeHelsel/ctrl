"""Prospective normalized toy contract adds speed-squared forcing during excitation.
No motor/hardware execution; direct two-axis force sensing is an explicit interface.
"""

import json
from fractions import Fraction as F
from pathlib import Path

eta = F(1, 100)
omega = F(10)
detune = F(1, 10)
nu_max = detune * (1 + eta)
gain = (1 + nu_max / omega) ** 2
leak = gain * eta / (1 - eta)
probe_force = 2 + 2 * gain
E = F(1, 40)
K = F(3, 5)
B = (E + leak * K) / (1 - leak)
D = K + B
post = K + 2 * B
assert probe_force < F(41, 10)
assert B < F(1, 8) and post < F(3, 4)
# e^6>400 is certified by a lower partial Taylor sum with nonnegative omitted terms.
term = F(1)
partial = term
for k in range(1, 21):
    term *= F(6, k)
    partial += term
assert partial > 400
travel6 = post + (probe_force - post) * F(7, 400)
assert travel6 < 1
# Nominal ramps10 each, hold20pi; using pi<22/7 gives finite completion bound83.
time_upper = 20 + 20 * F(22, 7)
assert time_upper < 83
out = {
    "status": "new prospective diagnostic contract; not original scalar model or a fitted wheel system",
    "phase_actuator": "relative speednu: nominal ramps0 to.1 in10 then onebeat holdT20pi then10 return; actual constant gain1+delta, |delta|<=.01; no unmodeled lag/load",
    "actual_relative_speed_bound": str(nu_max),
    "actual_relative_acceleration_bound": str(F(1, 100) * (1 + eta)),
    "baseline_speed": str(omega),
    "drivetrain_force_scaling": "(1+nu/10)^2 d0; wheel speed and reference fixed",
    "force_gain_max": str(gain),
    "leakage_bound_in_baseline_d_units": str(leak),
    "probe_force_bound": str(probe_force),
    "probe_travel_limit": str(F(41, 10)),
    "measurement": "direct two-axis force vectorIQ with gain/phase bound, error<=1/40 afterdemod; baselineerror<=1/10, b1,z.5. This is not inferred from a scalar displacement sensor.",
    "new_wheel_residual_bound": str(B),
    "baseline_nuisance_magnitude_bound": str(D),
    "post_correction_force_bound_any_nuisance_phase": str(post),
    "support": "complex xdd+2a*xd+a^2*x=f, a[1,2], initial|x|<=1,|xd+a*x|<=1; comparison gives|x|,|xd+a*x|<=probe_force",
    "handoff": "retainedstate, no reset; returnnominalspeed andapplywheelcorrectionc=-z throughgamma[0,1]; triangleconvexity retainsprobe_force bound",
    "post_handoff_travel6_upper": str(travel6),
    "post_handoff_comparison": "|x(s)|<=Fpost+(Fprobe-Fpost)*(1+s)*exp(-s); below1 foralls>=6; notrest",
    "exp6_lower_taylor20": str(partial),
    "excitation_duration_upper_using_pi22over7": str(time_upper),
    "limits": "Physical speed/torque authority, two-axis sensing/calibration and actual coupled support remain HOLD. Comparison/integral interfaces hand-derived, not a complete kernel hybrid-plant theorem. Travel thresholds4.1/1 are explicitly chosen for this prospective diagnostic, not predeclared historical requirements.",
}
out["finite_correction_ramp"] = (
    "Declared activeforce-phasor actuator: c(s)=-.5*(10s^3-15s^4+6s^5),s0to1,then-.5; |c|<=.5,|cdot|<=15/16<1; nojerk requirement. Not a claim of adding trialmass to movinghardware."
)
out["conditional_time_budget"] = (
    "Probe<83, correctionramp1, continued-forcecomparison6: travel<1 before90 timeunits; depends onallnewtoy sensing/actuation/plantpremises, not a hardwaredeadline."
)
Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
print(
    json.dumps(
        {
            k: v
            for k, v in out.items()
            if k
            in [
                "force_gain_max",
                "leakage_bound_in_baseline_d_units",
                "probe_force_bound",
                "new_wheel_residual_bound",
                "post_correction_force_bound_any_nuisance_phase",
                "post_handoff_travel6_upper",
            ]
        }
    )
)
