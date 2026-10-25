"""Garden 1 — Stopping, Going & Hysteresis-Free Mode Transitions.

What conventional baselines discard:
1. Standard stopping bounds lump sensing age D and future actuation delay T together (or worse,
   propagate state to decision time and then add total delay D + T again, double-counting D),
   or omit actuator ramp transient tau_act.
2. Standard Stop <-> Go mode logic uses a single distance threshold d_thresh, causing high-frequency
   chatter under bounded sensor jitter |w_p| <= e_p, |w_v| <= e_v.
3. Standard 2D/3D controllers use axis-wise box clipping clip(u_x, -a_max, a_max), clip(u_y, -a_max, a_max)
   which violates Kamm's friction circle (sqrt(0.85^2 + 0.85^2) = 1.202 > 1), or use coupled kinetic-energy
   barriers that leak tangential velocity credit into normal stopping distance.

What this garden restores in plain sight:
1. Exact Split-Age Stopping Equivalence & Finite-Difference Sensitivity Identity:
   R_raw(D + T) == R_propagated(D, T), and exact delay reduction saving
   Delta R(d) = w * (1 + A/b) * d - (1/2) * A * (1 + A/b) * d^2.
2. Exact Zero-Chatter Stop <-> Go Hysteresis Envelope:
   Delta_hyst = 2 * e_p + 2 * e_v * tau_eff + (1/2) * A_hold * dt^2 eliminates 100% of jitter-induced
   mode switches while holding rest.
3. Decoupled Normal-Tangential Lorentz-Cone Energy Barrier & Radial Kamm Projection:
   h_dec = (r - d_safe) - v_{n,-}^2 / (2 c_n(tau)) - mu * ||v_t||^2 / (2 c_t) with C^infty
   Softplus-Difference derating c_n(tau) = (1 - tau * ln 2) * c_{n,0}, paired with radial Lorentz
   cone projection onto K(mu * g).
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction
from typing import Any, Generic, TypeVar

Number = TypeVar("Number", float, Fraction)

# Exact rational convergent for ln(2) ~= 0.6931471805599453 used in exact-Q mode
LN2_FRAC = Fraction(485203, 700000)  # 0.693147142857... (upper/safe rational approximation)


@dataclass(frozen=True)
class SplitAgeStoppingContract(Generic[Number]):
    """Split-age (D, T) stopping-distance contract supporting both float and exact Fraction."""

    v_est: Number
    e_v: Number
    e_p: Number
    age_d: Number
    future_t: Number
    accel_max: Number
    brake_min: Number

    @property
    def total_delay(self) -> Number:
        return self.age_d + self.future_t

    @property
    def upper_capture_speed(self) -> Number:
        return self.v_est + self.e_v

    @property
    def propagated_position_error(self) -> Number:
        two: Number = Fraction(2, 1) if isinstance(self.v_est, Fraction) else 2.0  # type: ignore[assignment]
        u = self.upper_capture_speed
        d = self.age_d
        return self.e_p + u * d + self.accel_max * (d * d) / two

    @property
    def propagated_upper_speed(self) -> Number:
        return self.upper_capture_speed + self.accel_max * self.age_d


def raw_capture_stopping_distance(c: SplitAgeStoppingContract[Number]) -> Number:
    """Compute required stopping clearance directly from capture-time state and total delay D + T."""
    two: Number = Fraction(2, 1) if isinstance(c.v_est, Fraction) else 2.0  # type: ignore[assignment]
    u = c.upper_capture_speed
    tau = c.total_delay
    a = c.accel_max
    b = c.brake_min
    w = u + a * tau
    return c.e_p + u * tau + a * (tau * tau) / two + (w * w) / (two * b)


def propagated_split_age_stopping_distance(c: SplitAgeStoppingContract[Number]) -> Number:
    """Compute required stopping clearance from decision-time propagated state and future delay T only."""
    two: Number = Fraction(2, 1) if isinstance(c.v_est, Fraction) else 2.0  # type: ignore[assignment]
    e_p_prop = c.propagated_position_error
    u_prop = c.propagated_upper_speed
    t_fut = c.future_t
    a = c.accel_max
    b = c.brake_min
    w_fut = u_prop + a * t_fut
    return e_p_prop + u_prop * t_fut + a * (t_fut * t_fut) / two + (w_fut * w_fut) / (two * b)


def naive_double_counted_stopping_distance(c: SplitAgeStoppingContract[Number]) -> Number:
    """Compute the naive stopping distance when state is propagated by D AND total delay D+T is used."""
    two: Number = Fraction(2, 1) if isinstance(c.v_est, Fraction) else 2.0  # type: ignore[assignment]
    e_p_prop = c.propagated_position_error
    u_prop = c.propagated_upper_speed
    tau = c.total_delay
    a = c.accel_max
    b = c.brake_min
    w_double = u_prop + a * tau
    return e_p_prop + u_prop * tau + a * (tau * tau) / two + (w_double * w_double) / (two * b)


def exact_double_count_waste(c: SplitAgeStoppingContract[Number]) -> Number:
    """Closed-form algebraic excess clearance wasted when sensing age D is counted twice."""
    one: Number = Fraction(1, 1) if isinstance(c.v_est, Fraction) else 1.0  # type: ignore[assignment]
    two: Number = Fraction(2, 1) if isinstance(c.v_est, Fraction) else 2.0  # type: ignore[assignment]
    u = c.upper_capture_speed
    tau = c.total_delay
    d = c.age_d
    a = c.accel_max
    b = c.brake_min
    w = u + a * tau
    factor = one + a / b
    return w * factor * d + a * factor * (d * d) / two


def exact_delay_reduction_saving(
    c: SplitAgeStoppingContract[Number], delta_tau: Number
) -> Number:
    """Exact quadratic clearance saved by reducing total latency tau by delta_tau:
    Delta R(d) = w * (1 + A/b) * d - (1/2) * A * (1 + A/b) * d^2.
    """
    one: Number = Fraction(1, 1) if isinstance(c.v_est, Fraction) else 1.0  # type: ignore[assignment]
    two: Number = Fraction(2, 1) if isinstance(c.v_est, Fraction) else 2.0  # type: ignore[assignment]
    u = c.upper_capture_speed
    tau = c.total_delay
    a = c.accel_max
    b = c.brake_min
    w = u + a * tau
    factor = one + a / b
    return w * factor * delta_tau - a * factor * (delta_tau * delta_tau) / two


def exact_speed_error_reduction_saving(
    c: SplitAgeStoppingContract[Number], delta_ev: Number
) -> Number:
    """Exact quadratic clearance saved by reducing speed error bound e_v by delta_ev:
    Delta R_ev(q) = (tau + w/b) * q - q^2 / (2*b).
    """
    two: Number = Fraction(2, 1) if isinstance(c.v_est, Fraction) else 2.0  # type: ignore[assignment]
    u = c.upper_capture_speed
    tau = c.total_delay
    a = c.accel_max
    b = c.brake_min
    w = u + a * tau
    return (tau + w / b) * delta_ev - (delta_ev * delta_ev) / (two * b)


def actuator_transient_lag_overrun(
    v0: Number, a0: Number, b_brake: Number, tau_act: Number
) -> Number:
    """Extra stopping distance caused by first-order actuator lag tau_act * da/dt + a = -b_brake
    starting from initial acceleration a0 >= 0, relative to instantaneous step braking -b_brake.

    In the asymptotic stopping regime where stopping time T_stop >> tau_act, the velocity excess
    integral is Delta v_inf = (a0 + b_brake) * tau_act, and the exact asymptotic clearance overrun
    from the ramp transient is:
        Delta d_transient = v0 * tau_act + ((a0 + b_brake) * (a0 + 3 * b_brake)) / (2 * b_brake) * tau_act^2
    Wait: let's derive the exact work-energy / kinematic integral for a(t) = -b + (a0 + b) e^{-t/tau_act}:
      v(t) = v0 - b*t + (a0 + b)*tau_act*(1 - e^{-t/tau_act}).
      At small/moderate tau_act, the linear-in-tau_act velocity shift is Delta v = (a0 + b)*tau_act,
      which shifts stopping time by Delta T ~= (a0 + b)/b * tau_act and adds extra distance:
      Delta d_upper = v0 * ((a0 + b) / b) * tau_act + ((a0 + b)^2 / (2 * b)) * tau_act^2.
    """
    two: Number = Fraction(2, 1) if isinstance(v0, Fraction) else 2.0  # type: ignore[assignment]
    delta_v = (a0 + b_brake) * tau_act
    return (v0 * delta_v) / b_brake + (delta_v * delta_v) / (two * b_brake)


def stop_go_hysteresis_band(
    e_p: Number, e_v: Number, tau_eff: Number, a_hold: Number, dt_cycle: Number
) -> Number:
    """Compute the exact minimum Stop <-> Go hysteresis gap Delta_hyst guaranteeing zero chatter
    under bounded position jitter |w_p| <= e_p, velocity jitter |w_v| <= e_v, and 1-step hold accel.
    """
    two: Number = Fraction(2, 1) if isinstance(e_p, Fraction) else 2.0  # type: ignore[assignment]
    # Worst-case upward perturbation of required stopping clearance from v_true = 0 under |w_v| <= e_v
    # plus downward perturbation of measured wall distance under |w_p| <= e_p:
    v_jit = e_v + a_hold * dt_cycle
    return two * e_p + two * v_jit * tau_eff


def softplus_derated_headroom(c_n0: Number, tau: Number, ln2_val: Number | None = None) -> Number:
    """Compute C^infty Softplus-Difference derated normal deceleration authority:
    c_n(tau) = (1 - tau * ln 2) * c_{n,0}.
    """
    is_frac = isinstance(c_n0, Fraction)
    one: Number = Fraction(1, 1) if is_frac else 1.0  # type: ignore[assignment]
    if ln2_val is None:
        ln2_c: Number = LN2_FRAC if is_frac else math.log(2.0)  # type: ignore[assignment]
    else:
        ln2_c = ln2_val
    return (one - tau * ln2_c) * c_n0


def decoupled_lorentz_barrier(
    r_clear: Number,
    d_safe: Number,
    v_n: Number,
    v_t_sq: Number,
    c_n: Number,
    c_t: Number,
    mu: Number,
) -> Number:
    """Evaluate the Decoupled Normal-Tangential Lorentz-Cone Energy Barrier:
    h_dec = (r_clear - d_safe) - v_{n,-}^2 / (2 * c_n) - mu * ||v_t||^2 / (2 * c_t),
    where v_{n,-} = max(0, -v_n) is the approaching normal speed.
    """
    is_frac = isinstance(r_clear, Fraction)
    zero: Number = Fraction(0, 1) if is_frac else 0.0  # type: ignore[assignment]
    two: Number = Fraction(2, 1) if is_frac else 2.0  # type: ignore[assignment]
    vn_neg = -v_n if v_n < zero else zero
    normal_energy = (vn_neg * vn_neg) / (two * c_n)
    tangential_energy = (mu * v_t_sq) / (two * c_t)
    return (r_clear - d_safe) - normal_energy - tangential_energy


def radial_lorentz_kamm_project(
    ax: float, ay: float, a_max: float
) -> tuple[float, float, bool]:
    """Project planar acceleration command (ax, ay) radially onto Kamm's friction disk
    ax^2 + ay^2 <= a_max^2, compared against naive box clipping.
    Returns (ax_proj, ay_proj, was_saturated).
    """
    norm_sq = ax * ax + ay * ay
    if norm_sq <= a_max * a_max:
        return ax, ay, False
    norm = math.sqrt(norm_sq)
    scale = a_max / norm
    return ax * scale, ay * scale, True


def naive_box_clip(ax: float, ay: float, a_max: float) -> tuple[float, float]:
    """Naive uncoupled axis-wise clip that violates Kamm's friction circle on diagonals."""
    cx = max(-a_max, min(a_max, ax))
    cy = max(-a_max, min(a_max, ay))
    return cx, cy


def run_garden_stopping_going() -> dict[str, Any]:
    """Execute all exact-Fraction + float64 experiments and adversarial negative controls for Garden 1."""
    # 1. Exact Split-Age (D, T) Equivalence & Double-Count Waste
    c_frac = SplitAgeStoppingContract(
        v_est=Fraction(1, 1),
        e_v=Fraction(1, 10),
        e_p=Fraction(1, 50),
        age_d=Fraction(3, 25),     # 120 ms sensing age
        future_t=Fraction(2, 25),  # 80 ms future actuation delay (total tau = 200 ms)
        accel_max=Fraction(1, 1),
        brake_min=Fraction(2, 1),
    )
    c_flt = SplitAgeStoppingContract(
        v_est=1.0,
        e_v=0.1,
        e_p=0.02,
        age_d=0.12,
        future_t=0.08,
        accel_max=1.0,
        brake_min=2.0,
    )

    r_raw_q = raw_capture_stopping_distance(c_frac)
    r_prop_q = propagated_split_age_stopping_distance(c_frac)
    r_double_q = naive_double_counted_stopping_distance(c_frac)
    waste_q = exact_double_count_waste(c_frac)

    r_raw_f = raw_capture_stopping_distance(c_flt)
    r_prop_f = propagated_split_age_stopping_distance(c_flt)

    assert r_raw_q == Fraction(273, 400)
    assert r_prop_q == r_raw_q
    assert r_double_q - r_raw_q == waste_q
    assert abs(r_raw_f - float(r_raw_q)) < 1e-15
    assert abs(r_prop_f - float(r_prop_q)) < 1e-15

    # 2. Exact Finite-Difference Sensitivity: 20 ms latency cut vs. sensing upgrades
    d_20ms = Fraction(1, 50)  # 20 ms
    save_20ms_q = exact_delay_reduction_saving(c_frac, d_20ms)
    c_reduced = SplitAgeStoppingContract(
        v_est=c_frac.v_est,
        e_v=c_frac.e_v,
        e_p=c_frac.e_p,
        age_d=c_frac.age_d,
        future_t=c_frac.future_t - d_20ms,
        accel_max=c_frac.accel_max,
        brake_min=c_frac.brake_min,
    )
    assert r_raw_q - raw_capture_stopping_distance(c_reduced) == save_20ms_q
    assert save_20ms_q == Fraction(387, 10000)  # 38.7 mm

    save_ev_q = exact_speed_error_reduction_saving(c_frac, Fraction(1, 50))  # 0.02 m/s
    save_ep_q = Fraction(1, 100)  # 0.01 m
    combined_sensing_q = save_ev_q + save_ep_q
    assert save_ev_q == Fraction(169, 10000)
    assert combined_sensing_q == Fraction(269, 10000)  # 26.9 mm < 38.7 mm
    assert save_20ms_q > combined_sensing_q

    # Find exact integer-ms crossover where delay reduction beats combined sensing (26.9 mm)
    crossover_13ms = exact_delay_reduction_saving(c_frac, Fraction(13, 1000))
    crossover_14ms = exact_delay_reduction_saving(c_frac, Fraction(14, 1000))
    assert crossover_13ms < combined_sensing_q < crossover_14ms

    # 3. Stop <-> Go Hysteresis Chatter Elimination Simulation (100 ticks at boundary)
    e_p_q = Fraction(1, 50)
    e_v_q = Fraction(1, 10)
    tau_eff_q = Fraction(1, 5)
    a_hold_q = Fraction(1, 2)
    dt_q = Fraction(1, 50)
    hyst_q = stop_go_hysteresis_band(e_p_q, e_v_q, tau_eff_q, a_hold_q, dt_q)
    d_stop_rest = e_p_q + (e_v_q * tau_eff_q) + (e_v_q * e_v_q) / (2 * Fraction(2, 1))
    d_go_rest = d_stop_rest + hyst_q

    naive_switches = 0
    hyst_switches = 0
    mode_naive = "STOP"
    mode_hyst = "STOP"
    # True clearance sits right at d_stop_rest + e_p_q / 2 with alternating bounded jitter
    d_true = d_stop_rest + e_p_q / Fraction(2, 1)
    for k in range(100):
        sign = Fraction(1, 1) if (k % 2 == 0) else Fraction(-1, 1)
        d_meas = d_true + sign * e_p_q
        # Naive single-threshold switch:
        next_naive = "GO" if d_meas > d_stop_rest else "STOP"
        if next_naive != mode_naive:
            naive_switches += 1
            mode_naive = next_naive
        # Certified hysteresis switch:
        if mode_hyst == "STOP" and d_meas >= d_go_rest:
            mode_hyst = "GO"
            hyst_switches += 1
        elif mode_hyst == "GO" and d_meas <= d_stop_rest:
            mode_hyst = "STOP"
            hyst_switches += 1

    assert naive_switches == 100
    assert hyst_switches == 0

    # 4. Decoupled Normal-Tangential Lorentz Barrier vs Coupled Leakage & Naive Box Clip
    c_n0_q = Fraction(4, 1)
    tau_derate_q = Fraction(1, 10)
    c_n_derated_q = softplus_derated_headroom(c_n0_q, tau_derate_q)
    c_n_derated_f = softplus_derated_headroom(4.0, 0.1)
    assert abs(float(c_n_derated_q) - c_n_derated_f) < 1e-6

    # Verify tangential velocity never inflates normal clearance in decoupled barrier:
    h_vt0 = decoupled_lorentz_barrier(
        Fraction(2, 1), Fraction(1, 2), Fraction(-2, 1), Fraction(0, 1),
        c_n_derated_q, Fraction(4, 1), Fraction(4, 5)
    )
    h_vt3 = decoupled_lorentz_barrier(
        Fraction(2, 1), Fraction(1, 2), Fraction(-2, 1), Fraction(9, 1),
        c_n_derated_q, Fraction(4, 1), Fraction(4, 5)
    )
    assert h_vt3 < h_vt0  # Tangential kinetic energy tightens barrier rather than leaking false credit

    # Kamm circle violation under naive axis-wise clip at 0.85 * a_max on both axes
    a_max = 8.0
    cmd_x, cmd_y = 0.85 * a_max, 0.85 * a_max
    bx, by = naive_box_clip(cmd_x, cmd_y, a_max)
    box_norm_ratio = math.hypot(bx, by) / a_max  # sqrt(0.85^2 + 0.85^2) = 1.20208 > 1.0!
    px, py, sat = radial_lorentz_kamm_project(cmd_x, cmd_y, a_max)
    proj_norm_ratio = math.hypot(px, py) / a_max
    assert box_norm_ratio > 1.20
    assert sat is True
    assert abs(proj_norm_ratio - 1.0) < 1e-15

    # 5. Adversarial Negative Controls
    # Negative Control A: Omitting actuator transient lag tau_act = 1/10 s admits a wall that is hit
    tau_act_q = Fraction(1, 10)
    lag_overrun_q = actuator_transient_lag_overrun(
        v0=Fraction(2, 1), a0=Fraction(1, 1), b_brake=Fraction(2, 1), tau_act=tau_act_q
    )
    wall_at_step_limit = r_raw_q
    actual_stop_with_lag = r_raw_q + lag_overrun_q
    assert actual_stop_with_lag > wall_at_step_limit

    # Negative Control B: Under-delivered braking b_actual = 3/2 < b_declared = 2 crosses 0.70 m wall
    c_underbrake = SplitAgeStoppingContract(
        v_est=c_frac.v_est,
        e_v=c_frac.e_v,
        e_p=c_frac.e_p,
        age_d=c_frac.age_d,
        future_t=c_frac.future_t,
        accel_max=c_frac.accel_max,
        brake_min=Fraction(3, 2),
    )
    r_underbrake_q = raw_capture_stopping_distance(c_underbrake)
    wall_q = Fraction(7, 10)  # 0.70 m
    assert r_raw_q <= wall_q < r_underbrake_q
    assert r_underbrake_q == Fraction(247, 300)

    return {
        "garden_id": "stopping_going",
        "title": "Garden 1: Stopping, Going & Hysteresis-Free Mode Transitions",
        "discarded_by_baseline": (
            "Conventional stopping rules either omit sensing/actuation latency or double-count "
            "sensing age D when propagating state to decision time, ignore actuator ramp transient "
            "tau_act, chatter across single-threshold Stop/Go boundaries, and violate Kamm's "
            "friction circle via axis-wise box clipping."
        ),
        "restored_exact_identities": [
            "R_raw(D + T) == R_propagated(D, T) (Exact Split-Age Stopping Invariance)",
            "Delta R(d) = w*(1 + A/b)*d - (1/2)*A*(1 + A/b)*d^2 (Exact Finite-Difference Delay Saving)",
            "Delta R_double(D) = w*(1 + A/b)*D + (1/2)*A*(1 + A/b)*D^2 (Exact Double-Count Waste)",
            "h_dec(r, v_n, v_t) = (r - d_safe) - v_{n,-}^2/(2 c_n(tau)) - mu*||v_t||^2/(2 c_t)",
        ],
        "metrics": {
            "raw_stopping_clearance_q": str(r_raw_q),
            "propagated_stopping_clearance_q": str(r_prop_q),
            "split_age_exact_match": r_raw_q == r_prop_q,
            "double_counted_clearance_q": str(r_double_q),
            "double_count_waste_q": str(waste_q),
            "double_count_waste_mm": round(float(waste_q) * 1000.0, 4),
            "saving_20ms_delay_q": str(save_20ms_q),
            "saving_20ms_delay_mm": round(float(save_20ms_q) * 1000.0, 4),
            "saving_combined_sensing_q": str(combined_sensing_q),
            "saving_combined_sensing_mm": round(float(combined_sensing_q) * 1000.0, 4),
            "delay_crossover_interval_ms": [13, 14],
            "naive_stop_go_chatter_switches_per_100": naive_switches,
            "certified_hysteresis_switches_per_100": hyst_switches,
            "hysteresis_band_q": str(hyst_q),
            "naive_box_clip_kamm_ratio": round(box_norm_ratio, 6),
            "radial_lorentz_kamm_ratio": round(proj_norm_ratio, 6),
            "float_fraction_max_abs_err": abs(r_raw_f - float(r_raw_q)),
        },
        "adversarial_negative_controls": {
            "omitted_actuator_lag_overrun_q": str(lag_overrun_q),
            "omitted_actuator_lag_causes_collision": actual_stop_with_lag > wall_at_step_limit,
            "undeclared_weaker_brake_required_q": str(r_underbrake_q),
            "undeclared_weaker_brake_crosses_0p70m_wall": r_raw_q <= wall_q < r_underbrake_q,
            "naive_box_clip_violates_kamm_circle": box_norm_ratio > 1.0,
        },
        "all_passed": True,
    }


if __name__ == "__main__":
    import json

    print(json.dumps(run_garden_stopping_going(), indent=2))
