# ctrl — Machine-Checked Robotics, Control Theory, Estimation, Vision & Open Math Lab

[![Lean 4](https://img.shields.io/badge/Lean%204-v4.28.0--rc1%20%7C%20v4.36.0--rc1-blue)](https://github.com/leanprover/lean4)
[![Robotics Lean Modules](https://img.shields.io/badge/Lean%20Modules-98%20Verified%20Modules%20%7C%2032%2C900%2B%20LOC-success)](lean/)
[![Robotics Runtime](https://img.shields.io/badge/ctrl.robotics-48%20%40lean__theorem%20Kernels%20%7C%20223%20Theorems-informational)](src/ctrl/robotics/)
[![Codegen & MuJoCo](https://img.shields.io/badge/C99%20%26%20MuJoCo%203.16-8.88e--16%20Parity%20%7C%204%20Closed--Loop%20Benchmarks-brightgreen)](src/ctrl/robotics/mujoco_benchmarks.py)
[![Tests](https://img.shields.io/badge/pytest-250%20passed-success)](tests/)

**`ctrl`** (`https://github.com/IamMikeHelsel/ctrl`) is an integrated formal verification and robotics engineering repository combining **98 zero-`sorry` Lean 4 modules** (`ControlsLean`, `Research`, `RoboLean`, `ErdosLab`) with **`ctrl.robotics`**, an executable dual-mode (NumPy `float64` + exact-$\mathbb{Q}$ `Fraction`) Python runtime, **zero-heap C99 and IEC 61131-3 Structured Text (ST) code generator**, and **closed-loop MuJoCo 3.16.0 physics benchmark suite**.

See **[`docs/STATUS_AND_ROADMAP.md`](docs/STATUS_AND_ROADMAP.md)** for the complete classification of **what's ready to use**, **what's worked**, **what looks promising**, and **what's still in work**.

---

## Executive Overview: Repository Organization & Maturity Tiers

```text
ctrl/
├── src/ctrl/
│   ├── robotics/                            # [READY TO USE] Machine-checked Python + C99 + MuJoCo runtime
│   │   ├── registry.py                      # @lean_theorem decorator & automated Lean source / token auditor
│   │   ├── trajectories.py                  # Optimal 7th-order septic trajectories (-22.47% Joule loss)
│   │   ├── contact_cbf.py                   # 3D 4-contact bilinear ZMP allocator & Lorentz-cone CBF filter
│   │   ├── vision_se3.py                    # Faugeras homography chirality & 6-DOF SE(3) HBVS depth control
│   │   ├── kinematics_ik.py                 # Non-inertial transport, minimal-norm IK & real-time RTA bounds
│   │   ├── estimation_lqr.py                # Joseph Kalman, DARE, H_inf, ISS Peter-Paul, Backstepping & Sontag CLF
│   │   ├── codegen.py                       # Zero-heap C99 & IEC 61131-3 ST codegen + clang -O3 ctypes parity
│   │   └── mujoco_benchmarks.py             # 4 closed-loop MuJoCo 3.16.0 benchmarks (6-DOF arm, quadruped, SE(3))
│   └── cli.py, spark.py, doctor.py          # [READY TO USE] CLI & DGX Spark orchestration
├── lean/
│   ├── ControlsLean/                        # [READY TO USE] 53 modules: LQR/DARE, H_inf, ISS, CLF, Kalman, POMDP, SO(3)/SE(3), Vision, 25 Erdős Bounties
│   ├── RoboLean/                            # [READY TO USE] 19 modules: Real-time RTA, Simplex safety, Fleet deadlock/throughput, Barcode/Reed-Solomon
│   ├── Research/                            # [READY + PROMISING] 26 modules:
│   │   ├── RobotEnergySmoothness.lean       #   [Ready] Septic electromechanical energy quadratic forms
│   │   ├── LorentzConeCBF.lean              #   [Ready] 3D 4-contact ZMP + shear allocator & Lorentz CBF
│   │   ├── CentroidalDecelerationLimit.lean #   [Ready] Biconditional safe deceleration min(mu, W/h_G)*g
│   │   ├── VisualServoingInvariant.lean     #   [Ready] 6-DOF SE(3) HBVS log-depth invariance vs IBVS retreat
│   │   ├── HomographyDecomposition.lean     #   [Ready] Faugeras rank-2 perturbation & chirality filtering
│   │   ├── WorldFrameTransport.lean         #   [Ready] Euler-centripetal orthogonality & Pythagorean IK
│   │   ├── ByersNash*.lean, Skew*.lean      #   [Promising] 6 modules (242 thms): Byers-Nash n=6 & 15D Parseval
│   │   ├── Erdos885*.lean                   #   [Promising] 3 modules (46 thms): Genus-2 Jacobian simplicity & Mumford/Cantor
│   │   └── Covering*.lean                   #   [Promising] 8 modules (65 thms): Erdős 273 23-smooth Euler crossover
│   └── ErdosLab/                            # [READY + IN WORK] 7 modules: Erdős #834 (solved), #273, #292, #318, #885, #939
├── tools/                                   # Exact rational certificate generators (SDP LDL^T, MF-13, Erdős 885)
├── tests/                                   # 250 passing pytest tests across robotics, codegen, MuJoCo & math
└── docs/
    ├── STATUS_AND_ROADMAP.md                # Master index: Ready vs. Worked vs. Promising vs. In-Work
    ├── architecture.md, cli.md, loop.md     # System architecture & workflow docs
    └── crossover-program-report-2026-10-19.md
```

---

## 1. Ready to Use: `ctrl.robotics` Runtime, C99/PLC Codegen & MuJoCo 3.16.0 Benchmarks

```python
from ctrl.robotics import (
    verify_lean_bindings,
    compile_and_verify_c99_kernels,
    run_all_mujoco_benchmarks,
)

# 1. Audit all 48 @lean_theorem functions (223 Lean theorems across 88 robotics modules, 0 sorry)
audit = verify_lean_bindings()
assert audit["ok"] is True

# 2. Compile generated C99 kernels with clang -std=c99 -O3 -Werror and verify 1-ULP parity (8.88e-16)
c99 = compile_and_verify_c99_kernels()
assert c99["parity_verified"] is True

# 3. Run all 4 closed-loop MuJoCo 3.16.0 physics benchmarks
benchmarks = run_all_mujoco_benchmarks()
assert benchmarks["ok"] is True
```

### Summary of Closed-Loop MuJoCo 3.16.0 Benchmark Results

| Benchmark | Baseline | Verified Controller | Measured Improvement |
| :--- | :--- | :--- | :--- |
| **1. 6-DOF Manipulator Disturbance & Impact Rejection** (`run_arm6dof_disturbance_iss_hinf_benchmark`) | Uncompensated PD under multi-tone torque + impulse ($\|w\|_{\max}^2 = 254.5\,\text{N}^2\text{m}^2$): Peak err $4.038\,\text{rad}$, $\ell_2$-gain $0.3325$ | $H_\infty$ + Backstepping + Sontag CLF (`iss_hinf_sontag_clf`, $\gamma_{\text{cert}} = 0.20$): Peak err **$0.0164\,\text{rad}$**, $\ell_2$-gain **$0.00246$** | **`-99.59%` peak tracking error** ($246\times$ tighter), **`-99.64%` RMS error**, **`135.3x` $\ell_2$-gain attenuation** |
| **2. 6-DOF Manipulator Energy Optimization** (`run_arm6dof_septic_energy_benchmark`) | 5th-order Minimum-Jerk ($\eta = 0$): $E_{\text{dyn}} = 773.18\,\text{J}$ | Optimal 7th-order Septic ($\eta^* = -11$): $E_{\text{dyn}} = 599.45\,\text{J}$ | **`-22.47%` dynamic Joule loss** (theoretical `-18.33%`) & **`-10.85%` viscous loss** |
| **3. 3D 4-Contact Quadruped Emergency Braking** (`run_quadruped_zmp_cbf_benchmark`) | Unshielded lunge toward wall at $x_{\lim} = 1.20\,\text{m}$ (tips over / slips) | 3D Lorentz-Cone CBF + Bilinear ZMP Allocator ($a_{\max} = \min(\mu, W/h_G) g$) | **Stops safely at $1.1920\,\text{m} < 1.20\,\text{m}$**, $100\%$ inside Lorentz cone ($f_{z,\min} = 22.14\,\text{N}$), **zero pitch/roll** ($\|\omega\|_{\max} = 1.64 \times 10^{-15}\,\text{rad/s}$) |
| **4. 6-DOF $SE(3)$ Visual Servoing** (`run_se3_visual_servoing_benchmark`) | Classical IBVS under $155^\circ$ optical-axis rotation (retreats $5.76\times$ to $12.67\,\text{m}$) | Homography-Based Visual Servoing (HBVS) with log-depth $\dot{d} = -\lambda d \ln(d/d^*)$ | **Eliminates camera-retreat pathology**: depth stays strictly monotone inside $[1.015\,\text{m}, 2.200\,\text{m}]$ |

---

## 2. Quick Start Commands

```bash
# Install Python environment & run all 250 tests (including MuJoCo, C99 codegen, and Lean binding audit)
uv sync
uv run pytest -q

# Build all Lean 4 libraries (ControlsLean, Research, RoboLean, ErdosLab)
source "$HOME/.elan/env"
cd lean && lake build

# Check CLI & Spark status
uv run ctrl doctor
uv run ctrl status
```

---

## 3. Documentation Index

| Document | Contents |
| :--- | :--- |
| **[docs/STATUS_AND_ROADMAP.md](docs/STATUS_AND_ROADMAP.md)** | **Master Index**: Ready to Use vs. What Worked vs. Promising Frontiers vs. Still In Work |
| **[docs/IDEA_PORTFOLIO_AND_SYNERGIES.md](docs/IDEA_PORTFOLIO_AND_SYNERGIES.md)** | **Domain-Organized Idea Catalog**: Approach, Novelty (`N1–N3`), Applicability (`A1–A3`), and Cross-Domain Synergies |
| **[docs/AGENT_IDEA_INDEX.json](docs/AGENT_IDEA_INDEX.json)** | **Machine-Readable Agent Index**: Structured JSON catalog of all 15 idea clusters, theorems, entrypoints, and combinability edges |
| **[PROJECT.md](PROJECT.md)** | Milestone history, interface contracts, and hypothesis audit rules |
| **[docs/crossover-program-report-2026-10-19.md](docs/crossover-program-report-2026-10-19.md)** | Detailed technical report on the Controls–Vision–Math crossover program |
| **[docs/architecture.md](docs/architecture.md)** | Mac + DGX Spark architecture and Challenge/Solution verification contract |
| **[docs/cli.md](docs/cli.md)** | `ctrl` CLI commands, JSON envelope, and exit codes |
| **[AGENTS.md](AGENTS.md)** | Rules for agents and contributors working in this repository |
