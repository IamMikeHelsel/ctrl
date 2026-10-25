"""Slotine–Li adaptive tracking for the planar RR arm: numpy reference and C99 binding.

Sign conventions are those of ``ControlsLean/Robotics/ManipulatorTracking.lean``:

* ``trackingError``  q~ = q - q_d
* ``referenceVel``   dq_r = dq_d - Λ q~   (so ddq_r = ddq_d - Λ (dq - dq_d) for constant Λ)
* ``slidingError``   s = dq - dq_r = (dq - dq_d) + Λ q~   (``slidingError_eq_velError_add``)
* control            τ = Y(q, dq, dq_r, ddq_r) θ̂ - K_D s
* adaptation         dθ̂/dt = -Γ Yᵀ s

For the true plant M ddq + C dq + g = τ with Y θ = M ddq_r + C dq_r + g, the closed loop is
M ds + C s + K_D s = Y θ~ with θ~ = θ̂ - θ, and Γ⁻¹ dθ~/dt = -Yᵀ s. These are exactly the
``hcl`` and ``hadapt`` hypotheses of ``slotine_li_adaptive_lyapunov_deriv``; with skew
Mdot - 2C (``hskew``) it gives, for V = ½ sᵀ M s + ½ θ~ᵀ Γ⁻¹ θ~,

    dV/dt = -sᵀ K_D s.

The Lean theorem is the algebraic identity at one instant; that the arm model satisfies the
hypotheses (regressor identity, skew-symmetry) is checked numerically by the tests.
"""

from __future__ import annotations

import ctypes
import hashlib
import os
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

import numpy as np

from ctrl.robotics import planar_rr
from ctrl.robotics.registry import lean_theorem

MODULE = "ControlsLean.Robotics.ManipulatorTracking"
CSRC = Path(__file__).with_name("csrc")
C_SOURCE = CSRC / "ctrl_slotine_li.c"
C_HEADER = CSRC / "ctrl_slotine_li.h"
CFLAGS = ("-std=c99", "-O2", "-Wall", "-Wextra", "-Werror", "-pedantic", "-fPIC", "-shared")


@dataclass(frozen=True)
class SlotineLiOutput:
    tau: np.ndarray
    theta_dot: np.ndarray
    s: np.ndarray
    dq_r: np.ndarray
    ddq_r: np.ndarray
    Y: np.ndarray


@lean_theorem(
    MODULE,
    (
        "trackingError",
        "referenceVel",
        "slidingError",
        "slidingError_eq_velError_add",
        "slotineLiControl",
        "slotine_li_closed_loop_sliding",
        "slotine_li_lyapunov_deriv",
        "slotine_li_adaptive_lyapunov_deriv",
    ),
)
def slotine_li_torque(
    q, dq, q_d, dq_d, ddq_d, Lam, Kd, Gamma, theta_hat, g0: float = planar_rr.G0
) -> SlotineLiOutput:
    """Reference Slotine–Li adaptive law (τ = Yθ̂ - K_D s, dθ̂/dt = -Γ Yᵀ s)."""
    q, dq = np.asarray(q, float), np.asarray(dq, float)
    q_d, dq_d, ddq_d = (np.asarray(x, float) for x in (q_d, dq_d, ddq_d))
    Lam, Kd, Gamma = (np.asarray(x, float) for x in (Lam, Kd, Gamma))
    theta_hat = np.asarray(theta_hat, float)
    e = q - q_d
    dq_r = dq_d - Lam @ e
    ddq_r = ddq_d - Lam @ (dq - dq_d)
    s = dq - dq_r
    Y = planar_rr.regressor(q, dq, dq_r, ddq_r, g0)
    tau = Y @ theta_hat - Kd @ s
    theta_dot = -Gamma @ (Y.T @ s)
    return SlotineLiOutput(tau, theta_dot, s, dq_r, ddq_r, Y)


@lean_theorem(MODULE, ("slotine_li_adaptive_lyapunov_deriv", "skew_coriolis_power_cancel"))
def lyapunov(theta, theta_hat, q, s, Gamma_inv) -> float:
    """V = ½ sᵀ M(q) s + ½ θ~ᵀ Γ⁻¹ θ~ with θ~ = θ̂ - θ."""
    tt = np.asarray(theta_hat, float) - np.asarray(theta, float)
    M = planar_rr.mass_matrix(np.asarray(theta, float), np.asarray(q, float))
    return float(0.5 * s @ M @ s + 0.5 * tt @ np.asarray(Gamma_inv) @ tt)


# ---------------------------------------------------------------- C99 kernel (ctypes)

_P = ctypes.POINTER(ctypes.c_double)
_LIB: ctypes.CDLL | None = None


def compiler() -> str | None:
    return os.environ.get("CC") or shutil.which("cc") or shutil.which("clang")


def build_kernel(out_dir: Path | None = None) -> Path:
    """Compile the kernel into a shared library (cached by source hash, outside the repo)."""
    cc = compiler()
    if cc is None:
        raise RuntimeError("no C compiler found (set CC)")
    src = C_SOURCE.read_bytes() + C_HEADER.read_bytes() + " ".join(CFLAGS).encode()
    tag = hashlib.sha256(src).hexdigest()[:16]
    if out_dir is None:
        out_dir = Path(tempfile.gettempdir()) / "ctrl-kernels" / tag
    out_dir.mkdir(parents=True, exist_ok=True)
    ext = ".dylib" if sys.platform == "darwin" else ".so"
    lib = out_dir / f"libctrl_slotine_li{ext}"
    if not lib.exists():
        tmp = out_dir / f".{os.getpid()}{ext}"
        subprocess.run(
            [cc, *CFLAGS, f"-I{CSRC}", str(C_SOURCE), "-o", str(tmp), "-lm"],
            check=True,
            capture_output=True,
            text=True,
        )
        tmp.replace(lib)
    return lib


def load_kernel() -> ctypes.CDLL:
    global _LIB
    if _LIB is None:
        lib = ctypes.CDLL(str(build_kernel()))
        lib.ctrl_slotine_li_torque.argtypes = [_P] * 9 + [ctypes.c_double] + [_P] * 6
        lib.ctrl_slotine_li_torque.restype = ctypes.c_int
        lib.ctrl_planar_rr_regressor.argtypes = [_P] * 4 + [ctypes.c_double, _P]
        lib.ctrl_planar_rr_regressor.restype = None
        _LIB = lib
    return _LIB


def _arr(x, n: int) -> np.ndarray:
    a = np.ascontiguousarray(np.asarray(x, dtype=np.float64).reshape(-1))
    if a.size != n:
        raise ValueError(f"expected {n} values, got {a.size}")
    return a


def _ptr(a: np.ndarray):
    return a.ctypes.data_as(_P)


def slotine_li_torque_c(
    q, dq, q_d, dq_d, ddq_d, Lam, Kd, Gamma, theta_hat, g0: float = planar_rr.G0
) -> SlotineLiOutput:
    """Same contract as :func:`slotine_li_torque`, computed by ``ctrl_slotine_li_torque``."""
    lib = load_kernel()
    ins = [
        _arr(q, 2),
        _arr(dq, 2),
        _arr(q_d, 2),
        _arr(dq_d, 2),
        _arr(ddq_d, 2),
        _arr(Lam, 4),
        _arr(Kd, 4),
        _arr(Gamma, 25),
        _arr(theta_hat, 5),
    ]
    tau, td, s, vr, ar, Y = (np.zeros(n) for n in (2, 5, 2, 2, 2, 10))
    rc = lib.ctrl_slotine_li_torque(*map(_ptr, ins), float(g0), *map(_ptr, (tau, td, s, vr, ar, Y)))
    if rc != 0:
        raise RuntimeError(f"ctrl_slotine_li_torque returned {rc}")
    return SlotineLiOutput(tau, td, s, vr, ar, Y.reshape(2, 5))


def regressor_c(q, dq, v, a, g0: float = planar_rr.G0) -> np.ndarray:
    lib = load_kernel()
    Y = np.zeros(10)
    ins = [_arr(x, 2) for x in (q, dq, v, a)]  # keep the buffers alive across the call
    lib.ctrl_planar_rr_regressor(*map(_ptr, ins), float(g0), _ptr(Y))
    return Y.reshape(2, 5)
