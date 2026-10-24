---
title: If a quadratic energy drops every step, the state goes to zero.
subtitle: The discrete-time Lyapunov theorem for x(k+1) = A x(k). What it assumes, why it holds, a small and a larger worked example, and where it shows up in sampled-data control and estimation.
eyebrow: Explainer 01 · Controls · discrete-time stability
area: Controls
slug: discrete-lyapunov
lean: ControlsLean/Controls/DiscreteLyapunov.lean
theorems:
  - tendsto_pow_mulVec_zero
  - exists_lyapunov_contraction
  - PosDef.tendsto_pow_mulVec_zero
updated: 2026-10-24
---

## The idea in one picture {#idea}

A linear system $x_{k+1} = A x_k$ is stable when every starting state eventually returns to $0$. A finite simulation cannot settle that, because it only ever shows finitely many steps. Lyapunov's idea is to find one quadratic energy $V(x) = x^\top P x$ that is positive away from the origin and drops on every step. If such a $V$ exists, every trajectory has to slide down to $0$.

The picture shows the point of choosing $P$ with care. The plain length $\lVert x \rVert$ can go up on a step even when the system is stable. A well-chosen $V$ goes down on every step.

<figure class="ex-figure">
<!-- include: diagram.svg -->
<figcaption>Level sets of $V(x) = x^\top P x$ (solid) for the 2D example below, with the unit circle (dashed). The first step leaves the circle, so the length grew from 1.00 to 1.06. It still lands on a smaller ellipse, so $V$ fell from 5.61 to 4.61.</figcaption>
</figure>

## What the theorem says {#statement}

Take a real $n \times n$ matrix $A$ and run $x_{k+1} = A x_k$, so $x_k = A^k x_0$. Take any real $n \times n$ matrix $P$ and write $V(x) = x^\top P x$.

<div class="theorem-box">
<span class="label">Theorem · discrete-time Lyapunov</span>

If both quadratic forms below are positive for every nonzero $x$,

$$x^\top P x > 0 \qquad\text{and}\qquad x^\top \left(P - A^\top P A\right) x > 0 \qquad \text{for all } x \neq 0,$$

then every trajectory converges to the origin: $A^k x_0 \to 0$ as $k \to \infty$, for every $x_0$.

</div>

The two conditions read plainly:

- **$V$ is a real energy.** It is zero only at the origin and positive everywhere else.
- **One step loses energy.** Since $V(Ax) = (Ax)^\top P (Ax) = x^\top A^\top P A\, x$, the second condition says $V(x) - V(Ax) > 0$ for every $x \neq 0$.

Along the way the proof also shows a fixed rate: there is a $\rho$ with $0 \le \rho < 1$ and $V(Ax) \le \rho\, V(x)$ for all $x$. That is the separate theorem `exists_lyapunov_contraction`.

A detail worth noticing: the main version does not ask $P$ to be symmetric. A quadratic form only sees the symmetric part of $P$, so nothing is lost. The matrix-API version `PosDef.tendsto_pow_mulVec_zero` states the same result with Mathlib's `PosDef`, which does include symmetry.

Here is the Lean statement, with a translation:

```lean
theorem tendsto_pow_mulVec_zero [DecidableEq n] (hP : ∀ x ≠ 0, 0 < quad P x)
    (hQ : ∀ x ≠ 0, 0 < quad (P - Aᵀ * P * A) x) (x₀ : n → ℝ) :
    Tendsto (fun k : ℕ => (A ^ k) *ᵥ x₀) atTop (𝓝 0)
```

| Lean | Math |
| --- | --- |
| `quad P x` | $x^\top P x$ |
| `(A ^ k) *ᵥ x₀` | $A^k x_0$ |
| `Tendsto f atTop (𝓝 0)` | $f(k) \to 0$ as $k \to \infty$ |

## Why it holds {#why}

The proof has four steps. None of them computes an eigenvalue.

<ol class="steps">
<li><strong>One step, exactly.</strong> Write $Q = P - A^\top P A$. Then $V(Ax) = V(x) - x^\top Q x$ is an identity, not an estimate. It is two lines of matrix algebra (<code>quad_mulVec</code>, <code>quad_sub</code>).</li>
<li><strong>Compare both forms to length.</strong> A continuous function on the unit sphere reaches a minimum and a maximum, because the sphere is compact. The form $x^\top Q x$ is positive on the sphere, so its minimum $c_Q$ is positive. Scaling gives $x^\top Q x \ge c_Q \lVert x \rVert^2$ for every $x$. In the same way $V(x) \le C_P \lVert x \rVert^2$ for some $C_P > 0$ (<code>exists_quad_lower</code>, <code>exists_quad_upper</code>). In Lean, $\lVert x \rVert$ on $\mathbb{R}^n$ is Mathlib's default sup norm $\max_i \lvert x_i \rvert$, so the "sphere" is the boundary of a cube. Any norm works here; the constants change.</li>
<li><strong>Turn the loss into a fraction.</strong> Chain the bounds: $x^\top Q x \ge c_Q \lVert x \rVert^2 \ge (c_Q/C_P)\, V(x)$. Put that into step 1 to get $V(Ax) \le (1 - c_Q/C_P)\, V(x)$. Take $\rho = \max(1 - c_Q/C_P,\, 0)$, which is below 1 (<code>exists_lyapunov_contraction</code>).</li>
<li><strong>Repeat, then convert back to length.</strong> Induction gives $V(x_k) \le \rho^k V(x_0)$. Since $P$ is positive on the sphere too, step 2 gives $V(x) \ge c_P \lVert x \rVert^2$ with $c_P > 0$. So $\lVert x_k \rVert^2 \le \rho^k V(x_0) / c_P$, which goes to 0 (<code>tendsto_pow_mulVec_zero</code>).</li>
</ol>

Compactness of the sphere in step 2 is the only analytic ingredient. The rest is algebra and an induction, which is part of why the Lean proof stays short.

## A simple example {#simple}

Start with one number. Let $x_{k+1} = a\,x_k$ and take $P = 1$, so $V(x) = x^2$. The second condition becomes $1 - a^2 > 0$, and step 1 of the proof is exact here: $V(x_{k+1}) = a^2\, V(x_k)$.

- With $a = 0.8$: $1 - 0.64 = 0.36 > 0$. $V$ is multiplied by 0.64 on every step, and $x_k \to 0$.
- With $a = 1.1$: $1 - 1.21 = -0.21 < 0$. There is no certificate, and in this case the state does grow.

For a scalar, no other choice of $P$ changes the verdict, since $P - a^2 P = (1 - a^2) P$. The condition is exactly $\lvert a \rvert < 1$. In higher dimensions the choice of $P$ matters a great deal, which is the next example.

<figure class="ex-figure">
<video controls preload="metadata" playsinline width="1280" height="720" poster="media/ScalarLyapunov.png" aria-label="Animation of the scalar case: V shrinks by a squared each step for a = 0.8 and grows for a = 1.1"><source src="media/ScalarLyapunov.mp4" type="video/mp4"></video>
<figcaption>Scalar case. Bars show $V(x_k) = x_k^2$ on one shared scale for both values of $a$. About 50 seconds.</figcaption>
</figure>

## A harder example {#harder}

Now take a 2D system:

$$A = \begin{bmatrix} 1.0 & 0.6 \\ -0.35 & 0.6 \end{bmatrix}.$$

Its eigenvalues are $0.8 \pm 0.412\,i$, both with modulus $0.9$, so it is stable. Its operator norm is $\lVert A \rVert_2 \approx 1.17$, so some states get longer on a single step. Starting from $x_0 = (1, 0)$, the first step goes to $(1, -0.35)$, whose length is 1.06. The plain length $\lVert x \rVert$ is therefore not a Lyapunov function for this system.

A good $P$ comes from solving the linear Stein equation $A^\top P A - P = -I$, which is three unknowns here:

$$P \approx \begin{bmatrix} 5.61 & 2.81 \\ 2.81 & 7.88 \end{bmatrix}, \qquad P - A^\top P A = I.$$

The eigenvalues of $P$ are about 3.72 and 9.77, so $x^\top P x > 0$. And $x^\top (P - A^\top P A) x = \lVert x \rVert^2 > 0$. Both conditions hold, so the theorem applies.

| step $k$ | $x_k$ | $\lVert x_k \rVert$ | $V(x_k)$ |
| --- | --- | --- | --- |
| 0 | (1.000, 0.000) | 1.000 | 5.610 |
| 1 | (1.000, −0.350) | 1.059 | 4.610 |
| 2 | (0.790, −0.560) | 0.968 | 3.488 |
| 3 | (0.454, −0.612) | 0.762 | 2.550 |
| 4 | (0.087, −0.526) | 0.533 | 1.969 |

Over 14 steps the length goes up on steps 1, 6, 7, 13 and 14 (and by about $10^{-5}$ on step 8). $V$ goes down on every step and stays under $0.898^k\, V(x_0)$. The 0.898 is the true worst-case ratio $\max_x V(Ax)/V(x)$. With $Q = I$ it equals $1 - 1/\lambda_{\max}(P)$, which is the proof's $1 - c_Q/C_P$ computed with Euclidean constants. The Lean proof uses the sup norm, where $C_P \approx 19.1$, so its $\rho$ is looser, about 0.948. Both are below 1, which is all the theorem needs.

<figure class="ex-figure">
<video controls preload="metadata" playsinline width="1280" height="720" poster="media/PlaneLyapunov.png" aria-label="Animation of the 2D example: the state's length wobbles while V decreases on every step under a geometric envelope"><source src="media/PlaneLyapunov.mp4" type="video/mp4"></video>
<figcaption>2D case. Left: the state on smaller and smaller level sets of $V$, with the unit circle dashed. Right: length (not monotone) and $V$ (monotone, under the dashed envelope $\rho^k V(x_0)$). About 35 seconds.</figcaption>
</figure>

## Where it might apply {#applies}

The theorem is a check, not a search. Some other step produces a candidate $P$, and this result turns two finite matrix conditions into a statement about every trajectory. That pattern shows up in a few places.

<div class="applies">
<div><h3>Digital feedback loops</h3><p>A sampled controller $u_k = -K x_k$ gives the closed loop $x_{k+1} = (A - BK)\,x_k$. A $P$ from a Lyapunov or LMI solver, checked against both conditions, certifies the loop. In this repo, <code>dare_closedLoop_tendsto_zero</code> in <code>LQR.lean</code> uses this theorem to show the LQR closed loop is stable, given $P > 0$ solving the Joseph-form DARE and $Q + K^\top R K > 0$.</p></div>
<div><h3>Observers and filters</h3><p>A Luenberger observer's error follows $e_{k+1} = (A - LC)\,e_k$ (<code>observer_error_step</code> in <code>Observer.lean</code>). A certificate for $A - LC$ shows the estimate converges to the true state in the noise-free model.</p></div>
<div><h3>Linear iterative methods</h3><p>Jacobi, Gauss-Seidel and heavy-ball momentum on a quadratic all have error dynamics $e_{k+1} = M e_k$ for a fixed matrix $M$. When $M$ is non-normal ($\lVert M \rVert_2 > \rho(M)$), the plain error can grow for a few steps. If the spectral radius $\rho(M) < 1$, a certificate exists and proves convergence. Jacobi does not always meet that condition.</p></div>
<div><h3>Going the other way</h3><p>If $A^k x \to 0$ for every $x$, a certificate always exists. That converse is <code>converse_lyapunov_of_schur</code>: applied with $Q = I$ it gives a symmetric $S \succeq I$ with $S - A^\top S A = I$. It is in <code>SchurLyapunov.lean</code>, built on the Lyapunov sums in <code>ConverseLyapunov.lean</code>.</p></div>
</div>

## What it does not say {#limits}

<ul class="limits">
<li><strong>Model scope.</strong> Linear, time-invariant, noise-free, exact real arithmetic. No saturation, delay, switching or time-varying $A$.</li>
<li><strong>It does not find $P$.</strong> Finding one is a separate numerical step. The theorem certifies a $P$ you already have.</li>
<li><strong>The headline result gives no rate.</strong> <code>tendsto_pow_mulVec_zero</code> states convergence only. The rate is in <code>exists_lyapunov_contraction</code>, and only as "some $\rho < 1$ exists", not as a computed number.</li>
<li><strong>Floating point is not covered.</strong> A $P$ that passes a check in floating point is evidence, not a proof. Check with margin, or in exact rational arithmetic.</li>
<li><strong>One failed $P$ proves nothing.</strong> If the conditions fail for a given $P$, another $P$ may still work. In the scalar case every $P > 0$ gives the same verdict.</li>
</ul>

## Check it yourself {#check}

Build and audit the Lean file (axioms should be only `propext`, `Classical.choice`, `Quot.sound`):

```sh
scripts/check.sh ControlsLean/Controls/DiscreteLyapunov.lean
lake env lean scripts/Audit.lean | grep tendsto_pow_mulVec_zero
```

Print the numbers used on this page, then rebuild the diagram, the animations and the page:

```sh
cd site/explainers/discrete-lyapunov
uv run --no-project --with numpy example.py
uv run --no-project --with numpy diagram.py
cd ../../..
uv run --no-project --python 3.12 --with manim==0.22.0 --with numpy \
  tools/explainer/render.py discrete-lyapunov
uv run --no-project --with markdown-it-py --with pyyaml tools/explainer/build.py discrete-lyapunov
```
