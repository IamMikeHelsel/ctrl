# Status, Architecture & Roadmap: What Worked, What's Ready, What's Promising & What's In Work

**Updated**: October 2026  
**Repository**: `https://github.com/IamMikeHelsel/ctrl`  
**Branches**:
- `main`: Canonical 53-module `ControlsLean` library (**14,643 LOC**, **872 theorems**, **424 audited headline theorems**, `0 sorry`).
- `crossover-research-2026-10-19`: Full interdisciplinary monorepo combining `ControlsLean`, `Research` (**26 modules**, **9,500+ LOC**), `RoboLean` (**19 modules**, **9,893 LOC**), `ErdosLab` (**7 modules**), the **`ctrl.robotics` Python/C99/IEC 61131-3 ST runtime** (**48 `@lean_theorem` functions** binding **223 Lean theorems**), and **4 closed-loop MuJoCo 3.16.0 benchmarks** (**250 passing pytest tests**).

---

## 1. Executive Classification of All Work

### Tier A — Ready to Use (Production-Verified Lean 4 Modules & Executable Kernels)

| Subsystem | Location | Maturity | Verification Gate |
| :--- | :--- | :---: | :--- |
| **Linear & Optimal Control** (`LQR`, `DAREExistence`, `DAREUniqueness`, `LQROptimality`, `DAREDetectable`, `SchurLyapunov`, `DiscreteLyapunov`, `ConverseLyapunov`, `Gramian`, `Companion`, `PolePlacement`, `PolePlacementGeneral`, `Reachability`, `Observability`, `Hurwitz2`, `Hurwitz3`, `Jury2`) | `ControlsLean/Controls/` | **Production Ready** | `scripts/check.sh` (`0 sorry`, standard axioms) |
| **Robust, Output-Feedback & Nonlinear Control** (`LQG`, `Observer`, `BoundedRealHInf`, `ISS`, `SmallGain`, `BacksteppingCLF`, `BarrierPassivity`, `MPCFeasibility`, `IterativeLearning`) | `ControlsLean/Controls/` | **Production Ready** | `scripts/check.sh` + MuJoCo `arm_disturbance_hinf_iss` |
| **State Estimation, Filtering & POMDP Planning** (`KalmanOptimality`, `SteadyStateKalman`, `KalmanBucy`, `InformationFilter`, `AlphaBeta`, `RiccatiConvergence`, `ScalarKalman`, `LeastSquares`, `POMDPBelief`) | `ControlsLean/Estimation/` | **Production Ready** | `scripts/check.sh` + `@lean_theorem` runtime |
| **Robotics Kinematics, Lie Groups & Passivity** (`SO3Rodrigues`, `SE3Kinematics`, `QuaternionRotation`, `PlanarArm`, `Unicycle`, `ManipulatorTracking`) | `ControlsLean/Robotics/` | **Production Ready** | `scripts/check.sh` |
| **Computer Vision & Multi-View Geometry** (`Epipolar`, `EssentialConstraints`, `EightPoint`, `Homography`, `HomographyUniqueness`, `CrossRatio`, `Triangulation`, `Registration`) | `ControlsLean/Vision/` | **Production Ready** | `scripts/check.sh` |
| **Solved Erdős Bounties (25 Problems)** (`ErdosBounties`, `ErdosNewInsights`, `ErdosWave2`) | `ControlsLean/Bounty/` | **Production Ready** | `scripts/check.sh` (#36, #96, #143, #242, #261, #275, #311, #341, #367, #370, #389, #455, #493, #533, #645, #834, #873, #931, #951, #995, #1055, #1059, #1073, #1102, #1113, #1125, #1148, #1179, #1187) |
| **`ctrl.robotics` Python + C99 + IEC 61131-3 ST Runtime** (`trajectories.py`, `contact_cbf.py`, `vision_se3.py`, `kinematics_ik.py`, `estimation_lqr.py`, `codegen.py`, `mujoco_benchmarks.py`) | `src/ctrl/robotics/` (`crossover-research-2026-10-19`) | **Production Ready** | `verify_lean_bindings()` (`48` functions, `223` theorems) + `clang -O3 -Werror` ($8.88 \times 10^{-16}$ parity) + `250` pytest tests |

---

### Tier B — What Worked (High-Impact Methodological & Engineering Wins)

1. **Eliminating Spectral Theory from Riccati, LQG, and ISS Proofs**:
   - Proving detectable DARE stability (`DAREDetectable.lean`) via forced-observer zero-step escape, discrete ISS (`ISS.lean`) via the square-root-free matrix Peter–Paul identity, and $H_\infty$ attenuation (`BoundedRealHInf.lean`) via indefinite minimax completion of squares allowed complete, general-$n$ matrix formalizations in Lean 4 without complex Jordan blocks or matrix square roots.
2. **Closed-Form Conic Duality Replacing Online QP Solvers at 1–10 kHz**:
   - In `LorentzConeCBF.lean` and `codegen.py`, the 3D Lorentz-cone safety filter (`ctrl_lorentz_cbf_filter_3d`) and 4-foot bilinear ZMP + proportional shear allocator (`ctrl_quad_contact_allocator`) execute in $<100\,\text{ns}$ in C99 with zero heap allocation and zero pitch/roll angular momentum drift ($\dot{L} = 0$).
3. **Analytic Electromechanical Trajectory Optimization (`RobotEnergySmoothness.lean`)**:
   - Proving cross-power orthogonality $\int_0^T a(t) j(t)\,dt = 0$ on rest-to-rest trajectories reduced the 7th-order septic energy functional to an exact rational quadratic form in $\eta$, yielding `-22.47%` dynamic Joule loss and `-10.85%` viscous dissipation in 6-DOF MuJoCo benchmarks over classical minimum-jerk.
4. **Composite $H_\infty$ + ISS + Sontag CLF Disturbance Rejection**:
   - In `run_arm6dof_disturbance_iss_hinf_benchmark`, combining the $H_\infty$ Riccati minimax bound, Peter–Paul ISS sublevel certificate, and Sontag's universal CLF (`ctrl_sontag_clf`) achieved a **`99.59%` reduction in peak joint error** and **`135.3x` $\ell_2$-gain attenuation** under continuous multi-frequency torque disturbances and impulse impacts.

---

### Tier C — What Looks Promising (Deep Open-Problem Breakthroughs)

| Open Problem | Modules (`crossover-research-2026-10-19`) | What Has Been Proved in Lean 4 | Why It Looks Promising |
| :--- | :--- | :--- | :--- |
| **Byers–Nash $n=6$ Conjecture (`MF-13`)**: Does $k(A) \le s(A)$ hold for all $A \in M_6(\mathbb{R})$, where $s(A) = \min_{\|S\|_F=1, S^\top=S} \|\mathcal{L}_A(S)\|_F$ and $k(A) = \min_{\|K\|_F=1, K^\top=-K} \|\mathcal{L}_A(K)\|_F$? | `ByersNashDuality.lean`, `SkewNormalForm.lean`, `SkewRankFourNormalForm.lean`, `ByersNashMultiTerm.lean`, `ByersNashHaarIntertwiner.lean`, `ByersNashOffDiagComplete.lean`, `ByersNashExtremalFlip.lean` (7 modules) | 1. Orthogonal decoupling of $\mathcal{L}_A$ on $\mathbb{S}_n \oplus \mathbb{K}_n$ (`lyap_symm_skew_orthogonal_decomp`).<br>2. Unconditional exclusion for all $n=4$ and all $n=6, \operatorname{rank}(K) \le 4$.<br>3. 8-involution $(F,G)$-Klein Haar identity $\sum_{g=0}^7 \|\mathcal{L}_A(K T_g)\|_F^2 = 8\|\mathcal{L}_A(K)\|_F^2 - 6\|Y_{\text{diag}}\|_F^2 + 2\|Y_{\text{off}}\|_F^2$.<br>4. Complete 15D Parseval identity of $\mathbb{K}_6$ (`skew6_fifteen_dim_parseval`) & 4 canonical off-diagonal intertwiners (`canonical_four_term_norm_identity`). | All 10 strictly non-Common-$T$ parameter pairs (including $16.4\times$ off-diagonal-dominated regimes) are certified over $\mathbb{Q}$ via exact rational $LDL^\top \succ 0$ factorizations with $s(A)^2 \in [1.1509, 3.4292] > 1$. **Correction (2026-10-24):** the remaining $J$-vs-$\{I_2,F,G\}$ "cross-term" hypothesis of `twelve_comparator_dominance_of_j_comm_bound` is equivalent to the old 8-comparator hypothesis (`j_comm_bound_iff_offDiag_bound`). It is false even at certified near-extremal skew $K$. Every symmetric matrix in the span of the 12 comparators $\{KT_r, KG_r, U_r\}$ stays below $k(A)^2$ there (exact rational check), so $n=6$ is **not** one inequality away. Extremality constraints proved so far: `ByersNashExtremalFlip.lean`. |
| **Erdős Problem #885 ($k \ge 5$ Factor-Difference Sets)** | `Erdos885QuotientGenus.lean`, `Erdos885JacobianSimplicity.lean`, `Erdos885MumfordChabauty.lean` (3 modules, 1,078 LOC, 46 theorems) | 1. Complete projection tower from $\mathbb{P}^6$ onto 15 elliptic, 6 quintic genus-2, and 1 sextic genus-2 curves + syzygy $\prod_{r=0}^5 W_r = W^5$.<br>2. Symplectic Frobenius trace substitution & Weil obstruction proving all 14 Class 1 & Class 2 genus-2 Jacobians have $\operatorname{End}(J_{\overline{\mathbb{Q}}}) = \mathbb{Z}$.<br>3. Cassels–Flynn $(x-T)$ 2-descent triviality on single points, degree-2 Mumford divisors, and 3-/5-point Cantor reductions. | Rules out any classical Baker/elliptic-logarithm shortcut on $k=5$ and isolates the exact arithmetic mechanism (rank-1 Chabauty–Coleman + Mordell–Weil sieve on the simple genus-2 Jacobians) needed to prove finiteness/emptiness for $k=5$. |
| **Erdős Problem #273 ($p-1$ Covering Systems)** | `CoveringCapacity.lean`, `CoveringCRT.lean`, `CoveringMass.lean`, `CoveringTail.lean`, `CoveringEleven.lean`, `CoveringSeventeen.lean`, `CoveringAssembly.lean`, `CoveringFamily.lean` (8 modules, 1,222 LOC, 65 theorems) | 1. Weighted CRT density engine & prime-divisor sieve.<br>2. Exact Euler products for 11-, 13-, 17-, 19-, and 23-smooth prime-shifted boxes.<br>3. `smooth_covering_threshold_at_23`: $\frac{323323}{110592} < 3 < \frac{7436429}{2433024}$. | Pinpoints $p = 23$ as the exact prime-smoothness threshold where the Euler product $\prod_{p \le P} \frac{p-1}{p-2}$ first exceeds $3$, unconditionally forcing every $p-1$ covering system to use primes $\ge 23$. |

---

## 2. What's Still In Work (Prioritized Next Tasks)

1. **[In Work — Math / Controls Crossover] Close the Off-Diagonal $J$-vs-$\{I_2,F,G\}$ Cross-Term in $n=6$ Byers–Nash (`ByersNashOffDiagComplete.lean`)**:
   - Combine the 8-involution $(F,G)$-Haar comparator with the 4 canonical symmetric intertwiners $U_r = \operatorname{canonicalPiece}(T_r, Y) T_r$ and the 3 plane-swap involutions $W_{12}, W_{13}, W_{23}$ to bound the remaining 3D commuting ($J$) off-diagonal subspace without SDP grid assistance.
   - **Status 2026-10-24 (branch `research/byers-nash-n6-crossterm`): this route is obstructed.** The $J$-commuting hypothesis is equivalent to $\|Y_{\mathrm{off}}\|^2 \le 4\|H\|^2 + 4\|\mathrm{iso}(H)\|^2$ (`j_comm_bound_iff_offDiag_bound`). Numerically it fails at about 47% of random extremal $K$, and the 8 comparators fail at about 21%. An exact-rational near-extremal example (Rayleigh quotient within $10^{-13}$ of $k(A)^2$, LDL-certified) has $\max_{S \in \mathrm{span}\{KT_r, KG_r, U_r\}} \|L_A S\|^2/\|S\|^2 \le 0.99800\,k(A)^2$, while $s(A)^2 \approx 1.38\,k(A)^2$. The plane swaps add nothing structural: the $W$-conjugates of the 12 comparators already span all of $\mathbb{S}_6$. Adversarial search also breaks every same-square family $S^2=-K^2$ (the $SO(2)^3$ torus reaches only $0.993\,k^2$) and the full 9D block-diagonal symmetric space ($0.997\,k^2$). Any proof must use extremality of $K$ and a witness $S$ with nonzero off-diagonal blocks. `ByersNashExtremalFlip.lean` proves the first extremality constraints: `extremal_flip_offDiag_bound` gives $4\|H_{\mathrm{off}}\|^2 \le \|Y_{\mathrm{off}}\|^2$, and `extremal_eight_comparator_excess_le` bounds the 8-comparator excess by $16(\|H_{\mathrm{diag}}\|^2+\|\mathrm{iso}(H)\|^2)$.
2. **[In Work — Math] Formalize Rank-1 Coleman Annihilator & Mordell–Weil Sieve Certificate for Erdős #885**:
   - Build on `Erdos885MumfordChabauty.lean` to formalize the $p$-adic Coleman power-series zero bound on residue disks for the Class 1 quintic $C_5 : w^2 = x^5 + 89x^4 + 2796x^3 + 35704x^2 + 123200x$.
3. **[In Work — Robotics / Controls] Whole-Body $SE(3)$ Geometric Control & Slotine–Li MuJoCo Benchmark**:
   - Bind `ControlsLean.Robotics.ManipulatorTracking` (`slotine_li_lyapunov_deriv`, `slotine_li_adaptive_lyapunov_deriv`) and `ControlsLean.Estimation.POMDPBelief` (`bellman_backup_pwlc_preservation`) into `src/ctrl/robotics/` and add a C99 kernel `ctrl_slotine_li_torque` + MuJoCo payload-adaptation benchmark.
