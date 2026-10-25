"""Payload-adaptation benchmark: Slotine–Li adaptive vs fixed-parameter computed torque.

A planar RR arm (``planar_rr``) carries a tip payload the controllers don't know about. All
controllers start from the nominal (payload-free) parameters. Integration is pure numpy RK4
of the rigid-body model with the controller evaluated at every RK4 stage (continuous-time
control, no zero-order hold), so the continuous-time Lyapunov identity applies up to
integration error.

Controllers:

* ``adaptive``: Slotine–Li, τ = Yθ̂ - K_D s, dθ̂/dt = -Γ Yᵀ s (``slotine_li_torque``).
* ``slotine_li_fixed``: the same law with Γ = 0 (θ̂ stays nominal).
* ``ctc``: computed torque with nominal parameters, τ = M̂(ddq_d - K_v ė - K_p e) + Ĉ dq + ĝ,
  K_v = 2λ, K_p = λ² (critically damped at the same λ as the sliding surface Λ = λI).
  Its feedback stiffness M̂ λ² is lower than Slotine–Li's K_D Λ, so ``ctc_lambda10``
  (λ = 10) is reported too. Neither is an exact gain match; ``slotine_li_fixed`` is.

Lyapunov audit (adaptive run): V = ½ sᵀ M s + ½ θ~ᵀ Γ⁻¹ θ~. ``slotine_li_adaptive_lyapunov_deriv``
says dV/dt = -sᵀ K_D s whenever its hypotheses hold, and the plant here satisfies them, so
(a) the pointwise residual dV/dt + sᵀ K_D s is evaluated from the state, and (b) the
integrated balance V(t) - V(0) + ∫ sᵀ K_D s is tracked. A violation beyond RK4 error means a
kernel bug.

Run: ``uv run python -m ctrl.robotics.bench_slotine_li [--backend c] [--T 40]``.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass, field

import numpy as np

from ctrl.robotics import planar_rr
from ctrl.robotics.slotine_li import slotine_li_torque, slotine_li_torque_c

LAM = 4.0
KD = np.diag([30.0, 15.0])
GAMMA = 4.0 * np.eye(5)
CTC_HIGH_LAM = 10.0


def desired(t: float) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Sum-of-sines joint reference (persistently exciting for the five parameters)."""
    A = np.array([[0.8, 0.4], [0.7, 0.3]])
    w = np.array([[0.9, 2.1], [1.3, 2.9]])
    ph = np.array([[0.0, 0.3], [0.0, 0.5]])
    off = np.array([-1.0, 1.0])
    arg = w * t + ph
    q = off + (A * np.sin(arg)).sum(1)
    dq = (A * w * np.cos(arg)).sum(1)
    ddq = -(A * w**2 * np.sin(arg)).sum(1)
    return q, dq, ddq


@dataclass
class RunResult:
    controller: str
    rms_error: float
    rms_error_last_third: float
    max_error_last_third: float
    theta_error_initial: float
    theta_error_final: float
    payload_estimate: float | None
    lyapunov: dict = field(default_factory=dict)


def _ctc(theta_nom, q, dq, qd, dqd, ddqd, lam):
    e, de = q - qd, dq - dqd
    a = ddqd - 2.0 * lam * de - lam**2 * e
    M = planar_rr.mass_matrix(theta_nom, q)
    return M @ a + planar_rr.coriolis(theta_nom, q, dq) @ dq + planar_rr.gravity(theta_nom, q)


def simulate(
    controller: str = "adaptive",
    *,
    T: float = 40.0,
    dt: float = 1e-3,
    payload: float = 2.0,
    backend: str = "numpy",
    arm: planar_rr.ArmPhysical | None = None,
) -> RunResult:
    arm = arm or planar_rr.ArmPhysical()
    theta = planar_rr.params_from_physical(
        planar_rr.ArmPhysical(**{**asdict(arm), "payload": payload})
    )
    theta_nom = planar_rr.params_from_physical(arm)
    law = slotine_li_torque_c if backend == "c" else slotine_li_torque
    Lam = LAM * np.eye(2)
    Gamma = GAMMA if controller == "adaptive" else np.zeros((5, 5))
    Gamma_inv = np.linalg.inv(GAMMA)

    def control(t, x):
        q, dq, th = x[:2], x[2:4], x[4:]
        qd, dqd, ddqd = desired(t)
        if controller.startswith("ctc"):
            lam = CTC_HIGH_LAM if controller == "ctc_lambda10" else LAM
            return _ctc(theta_nom, q, dq, qd, dqd, ddqd, lam), np.zeros(5), None
        out = law(q, dq, qd, dqd, ddqd, Lam, KD, Gamma, th)
        return out.tau, out.theta_dot, out

    def f(t, x):
        tau, thd, _ = control(t, x)
        ddq = planar_rr.forward_dynamics(theta, x[:2], x[2:4], tau)
        return np.concatenate([x[2:4], ddq, thd])

    q0, dq0, _ = desired(0.0)
    x = np.concatenate([q0 + np.array([0.3, -0.2]), dq0, theta_nom])
    n = int(round(T / dt))
    errs = np.empty(n + 1)
    V = np.empty(n + 1)
    P = np.empty(n + 1)
    resid = np.empty(n + 1)

    def audit(k, t, x):
        q, dq, th = x[:2], x[2:4], x[4:]
        errs[k] = np.linalg.norm(q - desired(t)[0])
        if controller != "adaptive":
            return
        tau, thd, out = control(t, x)
        ddq = planar_rr.forward_dynamics(theta, q, dq, tau)
        s, sdot = out.s, ddq - out.ddq_r
        M = planar_rr.mass_matrix(theta, q)
        Md = planar_rr.mass_matrix_dot(theta, q, dq)
        tt = th - theta
        V[k] = 0.5 * s @ M @ s + 0.5 * tt @ Gamma_inv @ tt
        P[k] = s @ KD @ s
        Vdot = 0.5 * s @ Md @ s + s @ M @ sdot + tt @ Gamma_inv @ thd
        resid[k] = Vdot + P[k]

    audit(0, 0.0, x)
    for k in range(n):
        t = k * dt
        k1 = f(t, x)
        k2 = f(t + dt / 2, x + dt / 2 * k1)
        k3 = f(t + dt / 2, x + dt / 2 * k2)
        k4 = f(t + dt, x + dt * k3)
        x = x + dt / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
        audit(k + 1, t + dt, x)

    tail = errs[2 * n // 3 :]
    th_final = x[4:] if controller == "adaptive" else theta_nom
    d = planar_rr.payload_direction(arm)
    res = RunResult(
        controller=controller,
        rms_error=float(np.sqrt(np.mean(errs**2))),
        rms_error_last_third=float(np.sqrt(np.mean(tail**2))),
        max_error_last_third=float(tail.max()),
        theta_error_initial=float(np.linalg.norm(theta_nom - theta)),
        theta_error_final=float(np.linalg.norm(th_final - theta)),
        payload_estimate=(
            float(d @ (th_final - theta_nom) / (d @ d)) if controller == "adaptive" else None
        ),
    )
    if controller == "adaptive":
        work = np.concatenate([[0.0], np.cumsum(0.5 * dt * (P[1:] + P[:-1]))])
        balance = V - V[0] + work
        res.lyapunov = {
            "V0": float(V[0]),
            "V_final": float(V[-1]),
            "max_pointwise_residual": float(np.abs(resid).max()),
            "max_power": float(P.max()),
            "max_integrated_balance": float(np.abs(balance).max()),
            "max_V_increase_per_step": float(max(0.0, np.diff(V).max())),
        }
    return res


CONTROLLERS = ("adaptive", "slotine_li_fixed", "ctc", "ctc_lambda10")


def run_benchmark(**kw) -> dict:
    runs = [simulate(c, **kw) for c in CONTROLLERS]
    return {
        "config": {"payload": kw.get("payload", 2.0), "T": kw.get("T", 40.0)},
        "runs": [asdict(r) for r in runs],
    }


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--T", type=float, default=40.0)
    ap.add_argument("--dt", type=float, default=1e-3)
    ap.add_argument("--payload", type=float, default=2.0)
    ap.add_argument("--backend", choices=("numpy", "c"), default="numpy")
    ap.add_argument("--json", action="store_true")
    a = ap.parse_args(argv)
    out = run_benchmark(T=a.T, dt=a.dt, payload=a.payload, backend=a.backend)
    if a.json:
        print(json.dumps(out, indent=2))
        return
    print(f"payload {a.payload} kg, T = {a.T} s, dt = {a.dt}, backend = {a.backend}")
    print(
        f"{'controller':<18}{'RMS |e| rad':>12}{'RMS last 1/3':>14}{'|θ~| 0 → T':>18}{'m_p est':>9}"
    )
    for r in out["runs"]:
        mp = "" if r["payload_estimate"] is None else f"{r['payload_estimate']:.3f}"
        th = f"{r['theta_error_initial']:.3f} → {r['theta_error_final']:.3f}"
        print(
            f"{r['controller']:<18}{r['rms_error']:>12.2e}{r['rms_error_last_third']:>14.2e}"
            f"{th:>18}{mp:>9}"
        )
    print("Lyapunov audit (adaptive):", json.dumps(out["runs"][0]["lyapunov"]))


if __name__ == "__main__":
    main()
