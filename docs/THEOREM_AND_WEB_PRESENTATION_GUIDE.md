# Theorem Authoring, Technical Narrative & Web Presentation Guide

> **Purpose**: This guide codifies how we structure, prove, describe, benchmark, and present applied mathematics and formal control theorems in `ctrl`. It is designed as a self-contained playbook for authoring new modules and building internal or external project sites (including private internal portals).

---

## 1. How We Think About Theorems for Applied Engineering

Most formal verification projects stop at proving an abstract existence statement in Lean ($\exists u,\, \dot{V}(x,u) \le 0$), while most robotics/control repositories ship numerical solvers with no formal guarantees. Our core thesis is that **algebraic reformulation bridges both worlds**: when a control law or safety filter is expressed in closed form via completion of squares, conic projection, or boundary-factored polynomial bases, it becomes simultaneously **trivial to verify in Lean 4** (zero `sorry`, no fragile real-analysis limit proofs) and **deterministic to execute in C99** ($<100\,\text{ns}$, zero heap allocation, zero solver timeout risk).

### 1.1 The 4-Tier Verification & Deployment Architecture

Every production pillar follows a strict 4-tier pipeline, and our documentation always distinguishes what each tier guarantees:

| Tier | Artifact | Mathematical Domain | What It Guarantees | What It Does *Not* Claim |
| :--- | :--- | :--- | :--- | :--- |
| **Tier 1: Symbolic Proof** | `lean/ControlsLean/*.lean` | Exact $\mathbb{R}$ / $\mathbb{Q}$ / $\mathbb{Z}$ | Exact algebraic identities, Lie derivative dissipation ($\dot{V} \le -c\|e\|^2$), barrier forward invariance ($\dot{h} + \alpha h \ge 0$), conic membership ($\|f_{xy}\| \le \mu f_z$), and global optimality over $\mathbb{R}$. | Does not bound IEEE-754 floating-point roundoff or finite-step RK4 discretization error. |
| **Tier 2: Dual-Mode Reference** | `src/ctrl/*.py` (`@lean_theorem`) | `fractions.Fraction` ($\mathbb{Q}$) + `float` | Exact rational execution (`Fraction`) verifies that the executable algorithm satisfies the Lean theorem's rational inequalities with **zero rounding error** on rational test grids. | Does not guarantee hard real-time execution latency on embedded MCUs. |
| **Tier 3: Embedded Codegen** | `src/ctrl/c_codegen.py`, `plc_codegen.py` | IEEE-754 `double` (C99 / IEC 61131-3 ST) | Zero-allocation, loop-bounded C99 kernels verified to match the Python reference within $\le 8.88 \times 10^{-16}$ across randomized test suites, plus explicit branch guards against `NaN`/`Inf` when $L_g h \to 0$. | Numerical equivalence to Python is empirical ($\sim 10^{-16}$), not proved via a verified C compiler (CompCert). |
| **Tier 4: Physics Benchmark** | `src/ctrl/robotics/mujoco_benchmarks.py` | Discrete-time RK4 ($\Delta t = 1\text{–}2\,\text{ms}$) | Validates closed-loop performance under realistic multi-body dynamics (MuJoCo 3.16.0), actuator saturation, contact compliance, and external disturbances against **strong tuned baselines**. | Simulation benchmarks remain subject to sim-to-real transfer gaps (sensor noise, unmodeled structural compliance). |

---

### 1.2 Three Design Patterns for "Codegen-Ready" Lean 4 Theorems

When formulating a theorem in Lean 4 intended for real-time control or robotics, follow these three structural patterns:

#### Pattern A: Constructive Closed-Form Witness + Sum-of-Squares Optimality
Instead of proving that a convex optimization problem has a solution, define the explicit closed-form witness $u^*(x)$ and prove optimality via an algebraic completion of squares:
$$\text{Cost}(u) - \text{Cost}(u^*) = \|u - u^*\|_W^2 + \lambda_{\text{active}} \cdot (\text{constraint margin}) \ge 0.$$
* **Why it works in Lean 4**: `ring`, `nlinarith`, and `positivity` can discharge sum-of-squares decompositions deterministically.
* **Why it works in C99**: The witness formula $u^*(x)$ compiles directly into a few floating-point multiplies and a single branch on the active constraint sign.
* **Examples**:
  * `SafetyFilter.lean` (`rank1_cbf_safety_certified`, `rank1_cbf_pointwise_optimal`)
  * `FrictionCone.lean` (`project_friction_cone_valid`)

#### Pattern B: Exact Indefinite Completion of Squares for Minimax / $H_\infty$ Bounds
For disturbance attenuation ($\dot{V} \le -c\|e\|^2 + \gamma^2 \|w\|^2$), formulate the theorem as an exact algebraic identity first, then derive the inequality as a corollary:
$$2 e^T P (A_{\text{cl}} e + B w) + \frac{1}{\gamma^2}\|B^T P e\|^2 - \gamma^2 \|w\|^2 = e^T (P A_{\text{cl}} + A_{\text{cl}}^T P) e - \left\|\frac{1}{\gamma} B^T P e - \gamma w\right\|^2.$$
* **Why it works**: Proving the identity requires only `ring` (zero inequality reasoning), and the dissipation bound follows immediately from the non-negativity of the squared norm $\left\|\frac{1}{\gamma} B^T P e - \gamma w\right\|^2 \ge 0$.
* **Examples**:
  * `SontagCLF.lean` (`sontag_universal_clf_dissipation`)
  * `HInfinity.lean` (`riccati_minimax_completion_of_squares`)

#### Pattern C: Boundary-Factored Parametric Families for Trajectory Optimization
When optimizing a trajectory $\phi(s)$ over $s \in [0,1]$ subject to boundary conditions (e.g., $\phi(0)=0, \phi(1)=1, \dot{\phi}(0)=\dot{\phi}(1)=\ddot{\phi}(0)=\ddot{\phi}(1)=0$), parameterize the family as:
$$\phi_\eta(s) = \phi_{\text{base}}(s) + \eta \cdot p_{\text{null}}(s)$$
where $p_{\text{null}}(s) = s^3(1-s)^3(2s-1)$ vanishes to second order at $s \in \{0,1\}$.
* **Why it works**: Boundary conditions hold structurally for *every* $\eta \in \mathbb{R}$ by simple polynomial evaluation (`norm_num`). The integral cost $\int_0^1 \ddot{\phi}_\eta(s)^2\,ds$ reduces via polynomial integration to a 1D quadratic $A\eta^2 + B\eta + C$, whose global minimum $\eta^* = -B/(2A) = -11$ is proved by completing the square:
  $$J(\eta) - J(-11) = \frac{1}{2310}(\eta + 11)^2 \ge 0.$$
* **Examples**:
  * `Trajectory.lean` (`septic_optimal_eta_minimizes_acceleration_cost`)

---

## 2. How We Write About & Describe Theorems (Tone & Credibility Rules)

External reviewers, control engineers, and hiring/research leads evaluate interdisciplinary formal-methods + robotics work with high skepticism. A single overstated claim or weak baseline can undermine trust in the entire repository. Follow these six rules in all documentation, papers, and web pages:

### Rule 1: Lead with the Engineering Problem, Not the Mathematical Jargon
* **Avoid**: *"We prove a forced-observer zero-step escape via an 8-element Klein involution group and indefinite minimax completion of squares."*
* **Prefer**: *"On a 1–4 kHz embedded control loop, online QP safety filters can fail to converge or miss a timing deadline when contact constraints become nearly active. We prove an exact closed-form projection onto a safety halfspace and 3D Lorentz friction cone that executes in 28 ns in branch-bounded C99 with zero heap allocation."*
* **Principle**: State the physical system, the loop rate or operational constraint, and the concrete failure mode of standard practice *before* introducing the mathematical mechanism.

### Rule 2: Use Modest, Realistic Improvement Ranges Against Strong Baselines
* Never headline a `100x+` improvement against a naive strawman (such as an untuned low-gain PD controller under a massive impulse). Any competent control engineer knows that tuned high-gain Computed-Torque Control (CTC), $H_\infty$, or MPC will also beat plain PD.
* Always include a **strong tuned engineering baseline** in the benchmark suite and headline the improvement against *that* baseline:
  * **Disturbance Rejection**: Report the **`39.4%` peak tracking error reduction** ($27.1\,\text{mrad} \to 16.4\,\text{mrad}$) and **`39.6%` RMS error reduction** of Sontag CLF + $H_\infty$/ISS against **tuned high-gain CTC with sliding-mode damping** ($K_p = 416, K_d = 42$), while noting the naive PD number only as secondary context.
  * **Trajectory Energy**: Report both the **`4.1%` total actuator torque-squared reduction** ($\int \|\tau\|^2 dt$, where static gravity holding torque dominates) and the **`18.33%` theoretical / `22.47%` dynamic-only torque-squared reduction** ($\int \|\tau - g(q)\|^2 dt$).
  * **Safety Filter Latency**: Report **`28 ns`–`85 ns` deterministic execution** with **`0` solver timeouts** as a complementary last-resort guardrail alongside high-level MPC.

### Rule 3: Always Explain When Simulation Differs from Idealized Theory
If a simulated measurement beats or trails the idealized theoretical bound, **explain the physical mechanism immediately**:
* *Example (Septic $\eta = -11$ Trajectory)*: Theory predicts an exact $\frac{11}{60} = 18.33\%$ reduction in $\int_0^T \ddot{q}(t)^2\,dt$ for a linear double integrator. In our 6-DOF MuJoCo manipulator rollout, total actuator $\int \|\tau\|^2 dt$ drops by **`4.10%`** while dynamic-only $\int \|\tau - g(q)\|^2 dt$ drops by **`22.47%`**. Why both numbers?
  1. Gravity compensation $g(q)$ accounts for roughly $80\%$ of total holding effort during a slow rest-to-rest move, diluting the total actuator savings to $4.10\%$.
  2. Within the dynamic torque $\tau_{\text{dyn}} = M(q)\ddot{q} + C(q,\dot{q})\dot{q}$, the septic profile also lowers peak velocity slightly ($1.875$ vs. $2.055$), which reduces the quadratic Coriolis/centripetal term $C(q,\dot{q})\dot{q}$ on top of the $18.33\%$ inertial $M(q)\ddot{q}$ reduction, yielding $22.47\%$ dynamic savings.

### Rule 4: Be Transparent About the Verification Gap ("Proved vs. Tested")
Always include an explicit table or callout clarifying:
1. **What is formally proved in Lean 4** (continuous-time / algebraic properties over $\mathbb{R}$ or $\mathbb{Q}$, with exact module and theorem counts).
2. **What is verified by exact rational (`Fraction`) testing** (that the Python implementation matches the symbolic algebra with zero rounding error).
3. **What is checked by floating-point parity tests** (that generated C99 matches Python `float` to $\le 8.88 \times 10^{-16}$ and handles $L_g h \to 0$ singularities cleanly).
4. **What is evaluated empirically in MuJoCo** (discrete-time RK4 rollout with finite $\Delta t$).

### Rule 5: Keep Pure-Math / Community Formalizations Clearly Separated
If the project includes pure-math formalizations (such as Erdős problems from DeepMind's `formal-conjectures` repository), **never mix them into the robotics/control headline claims**:
* Frame them explicitly as **community service contributions**: formalizing *already-published literature theorems* (by Erdős, Sárközy, Pomerance, Graham, etc.) or finite small-$n$ base cases for the Lean 4 community.
* Place them in a collapsible appendix (`<details>`) at the bottom of the page with exact citations to the original paper and the exact scope of the Lean theorem (e.g., *"Formalizes the $n=4$ case of..."* or *"Formalizes Pomerance's published upper-bound construction for..."*).

### Rule 6: Trace Every Claim to Three Concrete Identifiers
Every technical card or section should give the reader three verifiable anchors:
1. **Lean 4 Theorem**: e.g., `ControlsLean/SafetyFilter.lean :: rank1_cbf_safety_certified`
2. **Python Dual-Mode Kernel**: e.g., `ctrl.safety_filter.cbf_safety_filter_1d`
3. **Generated C99 Function**: e.g., `ctrl_cbf_safety_filter_1d(u_nom, a, b, h, alpha)`

---

## 3. Anatomy of an Application Pillar (2 Paragraphs + Scientific Visual)

When writing up a core technical pillar for a site or design doc, use a consistent **two-paragraph + scientific animation** structure:

### Paragraph 1: Domain Application & Operational Bottleneck
* **Sentence 1**: Name the physical domain and control loop regime (e.g., *1–4 kHz whole-body torque control on a 12-DOF quadruped* or *high-duty-cycle 6-DOF industrial pick-and-place*).
* **Sentence 2–3**: Explain what standard engineering practice does today and where it breaks down (e.g., *online active-set QP solvers can exceed the 250 $\mu$s budget during multi-contact transitions*, or *classical image-based visual servoing under a $160^\circ$ wrist roll commands the camera to retreat $5.76\times$ backward along the optical axis*).

### Paragraph 2: Mathematical Solution, Formal Guarantee & Benchmark Result
* **Sentence 1–2**: State the closed-form mathematical mechanism in plain technical language and name the Lean 4 theorem that certifies it (e.g., *`rank1_cbf_safety_certified` proves via completion of squares that the closed-form rank-1 projection onto the safety halfspace and 3D Lorentz friction cone preserves $\dot{h} + \alpha h \ge 0$ and $\|f_{xy}\| \le \mu f_z$*).
* **Sentence 3–4**: State the C99 runtime profile and the MuJoCo benchmark result against a strong baseline (e.g., *In 3D 4-contact quadruped emergency braking at $1.9\,\text{m/s}$, the $28\,\text{ns}$ filter halts the robot at $0.961\,\text{m}$ before the $1.20\,\text{m}$ wall while maintaining $f_{z,\min} \ge 32.6\,\text{N}$ with zero solver timeouts*).

### Scientific Visual / Animation Standard
Every core pillar should include a data-driven animation (`.gif` or `.mp4`) generated directly from actual physics rollouts (`tools/generate_site_gifs.py`):
* **Visual Style**: Dark scientific theme (`#0b0d12` figure background, `#121620` axes background, `#1e2436` subtle gridlines, high-contrast semantic colors: `#f87171` red for uncertified/baseline failure, `#fbbf24` amber for strong conventional baseline, `#34d399` emerald / `#5b8cff` blue for the Lean-certified kernel).
* **Multi-Panel Layout ($880 \times 495$, 16:9)**:
  * **Left Panel**: Physical / geometric trajectory (3D robot/camera posture, phase portrait, or instantaneous power profile) with synchronized time playheads.
  * **Right Panel(s)**: Time-series of the exact certified quantity (barrier $h(t) \ge 0$, cumulative dynamic thermal energy $\int \|\tau_{\text{dyn}}\|^2 dt$, tracking error $\|e(t)\|_2$, or optical depth $Z(t)$) annotated with the Lean theorem equation.

---

## 4. Web Presentation & Internal Portal Guidelines

When building or maintaining the web interface (either on GitHub Pages or an internal Google site), adhere to the following structural and frontend engineering guidelines:

### 4.1 Page Information Architecture (7 Sections)
1. **Header & Hero**:
   * Concise subtitle explaining the 4-tier pipeline (`Lean 4 -> Dual-Mode Python -> C99/PLC -> MuJoCo`).
   * 4 headline metric cards with honest qualifiers (e.g., `53 Core / 98 Total` zero-`sorry` modules, `28–85 ns` C99 filter latency, `-4.1% Total / -22.5% Dynamic` torque-squared energy, `-39.4% vs. Tuned CTC` disturbance peak error).
2. **Section 1 — Four Core Application Pillars**:
   * Full-width horizontal cards on desktop (`grid-template-columns: 1.05fr 0.95fr`), pairing the two-paragraph domain narrative + metrics + traceability links on the left with the 16:9 scientific MuJoCo animation on the right.
3. **Section 2 — End-to-End Example (Theorem $\to$ C99 $\to$ Equivalence)**:
   * Side-by-side code blocks showing the exact Lean 4 theorem (`rank1_cbf_safety_certified` & `rank1_cbf_pointwise_optimal`) next to the generated C99 function (`ctrl_cbf_safety_filter_1d`), followed by a 3-point explanation of why they are equivalent and where floating-point guards apply.
4. **Section 3 — "What Is Proved vs. What Is Tested" Table**:
   * Explicit 4-row table mapping each layer (`Lean 4`, `Python Dual-Mode`, `C99 Codegen`, `MuJoCo Benchmarks`) to its exact scope, coverage numbers (`53/98` modules, `48/223` `@lean_theorem` bindings), and known limitations.
5. **Section 4 — Multi-Module Application Blueprints**:
   * 2x2 grid showing how individual verified primitives compose into complete engineering pipelines (Legged Locomotion Safety Stack, High-Duty-Cycle Pick-and-Place, Disturbance-Resilient Assembly, Singularity-Free Visual Servoing).
6. **Section 5 — Filterable Domain Catalog**:
   * Interactive status filter (`All`, `Ready to Use`, `Promising / Validated`, `In Work`) covering the 9 engineering domains with novelty ratings, applicability ratings, and combinability tags.
7. **Section 6 — Collapsible Community Formalization Appendix**:
   * A `<details>` disclosure block at the bottom of the page documenting the formalizations of published literature solutions for DeepMind's `formal-conjectures` repository, with explicit problem numbers, authors of the original proofs, and exact theorem scope.

### 4.2 Modern Web Engineering Standards
* **Zero External Runtime Dependencies**: Use semantic HTML5 and modern CSS (custom properties, CSS Grid, `<details>`/`<summary>`, `data-status` attribute selectors) so the site can be hosted statically anywhere (GitHub Pages, internal static file servers, or offline bundles) without build-step fragility.
* **Size-Aware & Layout-Shift-Free Styling (`CLS = 0`)**:
  * Use fluid typography (`clamp(1.65rem, 3vw, 2.3rem)`) and intrinsic grids (`repeat(auto-fit, minmax(320px, 1fr))`).
  * Always set explicit `width="880" height="495"` attributes and `aspect-ratio: 16 / 9` CSS on `.pillar-visual img` containers so the browser reserves exact layout space before GIFs load.
* **Image Fetch Priority**:
  * Set `fetchpriority="high"` on the first above-the-fold pillar animation (`pillar1_lorentz_cbf.gif`) to optimize Largest Contentful Paint (LCP).
  * Set `loading="lazy"` (without `fetchpriority="low"`) on all below-the-fold animations (`pillar2_septic_energy.gif`, `pillar3_sontag_hinf.gif`, `pillar4_se3_servoing.gif`).

---

## 5. Copy-Paste Templates for New Pillars & Theorems

### 5.1 Python `@lean_theorem` Binding Template

```python
from fractions import Fraction
from typing import Union
from ctrl._lean_bridge import lean_theorem

Scalar = Union[float, Fraction]

@lean_theorem(
    theorem="rank1_cbf_safety_certified",
    lean_file="lean/ControlsLean/SafetyFilter.lean",
    description=(
        "Closed-form rank-1 Control Barrier Function (CBF) projection: "
        "minimizes (u - u_nom)^2 subject to a + b*u + alpha*h >= 0."
    ),
    assumptions=["b != 0 when safety constraint is violated (margin < 0)"],
)
def cbf_safety_filter_1d(
    u_nom: Scalar, a: Scalar, b: Scalar, h: Scalar, alpha: Scalar
) -> Scalar:
    margin = a + b * u_nom + alpha * h
    if margin >= 0:
        return u_nom
    if abs(b) < 1e-12:
        return u_nom
    return u_nom - margin / b
```

### 5.2 Web Pillar Card HTML Template

```html
<div class="pillar-card">
  <div>
    <span class="domain-tag">Domain Name &bull; Operational Regime</span>
    <h3>Pillar Title: Plain-Spoken Engineering Capability</h3>
    <p>
      <strong>Domain Application:</strong> [2-3 sentences describing the physical system,
      loop rate, and why standard solvers/controllers fail or degrade in this regime.]
    </p>
    <p>
      <strong>What We Proved &amp; Tested:</strong> [2-3 sentences explaining the closed-form
      mathematical reformulation, the Lean 4 theorem name, and the MuJoCo benchmark result
      against a strong tuned engineering baseline.]
    </p>
    <div class="pillar-metrics">
      <div class="pm-item">
        <div class="pm-val">[Key Metric 1]</div>
        <div class="pm-lbl">[Baseline vs. Certified]</div>
      </div>
      <div class="pm-item">
        <div class="pm-val">[Key Metric 2]</div>
        <div class="pm-lbl">[Runtime / Latency]</div>
      </div>
    </div>
    <div class="pillar-links">
      Lean: <code>ControlsLean/Module.lean :: theorem_name</code> &bull;
      Python: <code>ctrl.module.func_name</code> &bull;
      C99: <code>ctrl_func_name</code>
    </div>
  </div>
  <div class="pillar-visual">
    <img src="assets/pillar_animation.gif"
         alt="Scientific simulation comparing strong baseline vs. Lean-certified controller"
         width="880" height="495" loading="lazy" />
    <div class="pillar-caption">
      <strong>MuJoCo 3.16.0 RK4 Rollout:</strong> [1-2 sentence caption explaining left and right panels.]
    </div>
  </div>
</div>
```

---

## 6. Theorem Explainers

Pillar cards sell a capability. Explainers teach one theorem: what it says, why it holds, a
simple and a harder worked example with short manim animations, where it might apply and
where it stops. They live in `site/explainers/<slug>/`, are built by `tools/explainer/`, and
follow `.claude/skills/theorem-explainer/SKILL.md`. Rules 1, 4 and 6 above apply unchanged;
explainers add a required "What it does not say" section and an independent claims audit
(`.claude/agents/explainer-auditor.md`) before publishing.
