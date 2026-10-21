# R12 supplement — causal hold allowance and remaining small-gain obligations

This supplements the initial review, not an extended investigation. Read original `ReferenceHistory.receive`, `ReferenceHistory.at`, and the update loop in run_smoke.py. No original edits. Exact audit: inventor_hold.py/json; inherited root model identifier unavailable.

## Causal reference and derivative availability

Original receive checks `issue ≤ arrival ≤ now ≤ execute`, increasing epoch, and nondecreasing execution times. It appends `(execute, target−previous_authoritative_target)` and retains every previous event. For the queued case, second goal is issued0.55s, arrives0.61s, executes0.67s; delta is−0.06rad relative to prior authoritative target+0.04rad, not relative to the current partially completed reference.

For a new event, F and its first three derivatives vanish through its execution time. Therefore receipt at0.61s changes neither current reference nor current analytic velocity/acceleration/jerk. At0.67s the new contribution is still zero through order3; the old history continues unchanged. Exact audit values for retained old `(q,v,a,j)`:

| Time | q | v | a | j |
|---|---:|---:|---:|---:|
| 0.55 | 1071677/96000000 | 27149/240000 | 413/800 | −19/4 |
| 0.61 | 1792157/96000000 | 31883/240000 | 77/800 | −37/4 |
| 0.67 | 4067/153600 | 47/384 | −13/32 | −25/4 |

The new term is `(0,0,0,0)` at all three times. Derivatives are computed from received command history, not measured plant derivatives and not future goal preview. A future event can appear in the mathematical completed-history formula without anticipatory influence because its support is causal. This equivalence relies on receiving it before it can become active.

Negative control: replacing old history by a constant at arrival would produce a velocity jump of−31883/240000rad/s. Thus retaining the tails is essential; “reset to current position” would invalidate the smooth-history argument even if it preserved position. Snap is not covered by a C3 continuity claim: the new event’s fourth derivative has a right jump of−75/2rad/s4 at commit. Source explicitly exposes derivatives0..3, not a continuous snap promise.

## Exactly what the 0.2mrad hold allowance assumes

For the fixed two-event history and h=0.2s, nonnegative kernel bounds give `−1/5 ≤ qdot ≤ 2/15`rad/s. For a sample time tk and `tk≤t<tk+0.001`, exact command `u(t)=q(tk)` obeys `|q(t)−u(t)|≤1/5000`rad by integrating qdot. This remains valid across an execution time because q is continuously differentiable and the global derivative bound holds there. The command itself still jumps at sample boundaries.

Required bindings:

- Same original two amplitudes and retained history. Additional revisions require recomputing positive/negative amplitude budgets; the old1/5rad/s bound is not automatically renewable.
- Correct commanded joint and home offset. The bound is a joint1 command-value error; other coordinates need their own model/error bounds.
- Exact zero-order hold on the stated1kHz update clock, with no extra transport/filter delay. For bounded age A instead, the same ideal Lipschitz argument gives `(1/5)A`; A must include actual effective command age.
- No late activation hidden by the proof. Original fixed packets arrive and execute on1ms ticks and pass the receive guard. Off-grid arrivals are processed only at command ticks; a packet processed after its execution time is rejected by the implementation. The current proof is not a packet-loss, jitter, deadline-miss, or recovery proof.
- Floating evaluation error is separate. The source-bound exact comparison found at most2.5e−17rad discrepancy at the2001 saved queued samples; that does not establish a universal runtime numerical bound.
- The exact derivative information is available causally to an implementation that evaluates history. The present plant receives only sampled position commands; it does not receive analytic velocity/acceleration/jerk as actuation channels. Passing those values as new feedforward inputs would change the architecture.

## A complete conditional small-gain statement

Let e be a declared coupled error state, potentially in an explicitly invertible coordinate change. Suppose, on a specified region and almost everywhere, an absolute-error comparison holds:

`D+ |e| ≤ A(t)|e| + G(t) wbar`,

with Metzler A(t), nonnegative G(t), and a bounded nonnegative input vector wbar including the held-reference value error. If one common p>0 and alpha>0 satisfy `A(t)p ≤ −alpha p` uniformly and `max_i (G(t)wbar)_i/p_i ≤ beta`, then `V=max_i |e_i|/p_i` satisfies `D+V≤−alpha V+beta`. Consequently a radius r is invariant when `V(0)≤r` and `beta≤alpha r`, subject to well-posedness and staying in the region where the comparison is valid. A first-exit argument must close that last obligation.

Remaining proof obligations are substantive:

1. Derive the actual coupled comparison inequality from the pinned plant/controller, including inertia, bias cancellation, friction, saturation, reference forcing, and admissible disturbances. Neither the recorded trace nor our toy matrix supplies it.
2. Bind p, alpha, input channels, state coordinates, initial set, and validity region. Pointwise stable matrices with different weights do not supply a common comparison certificate. Direct position/velocity absolute coordinates may fail to admit such a certificate even for a stable plant; an alternative valid norm or coordinate map may be necessary.
3. Treat command error as a bounded **value** channel if the servo model permits. Do not differentiate the staircase error and insert a finite derivative bound: its derivative contains impulses. If the controller differentiates or filters commands, include that actual interface state/model instead.
4. Prove saturation/total-torque bounds on the same invariant region, including all assistance channels and transmission. If clipping changes the equations, the old unsaturated comparison cannot be reused silently.
5. Convert the complete joint-state tube to the requested flange-position tube through a region-valid kinematic bound. Do not replace this with a point Jacobian, drop uncommanded joints, or claim orientation/tool bounds absent from the task.

Thus the0.2mrad allowance is a useful, causally valid input contract for the fixed ideal history. The missing result is the actual closed-loop MIMO gain and total-actuation certificate. No extension to a physical Franka variant is established.

## Scope correction: original reference versus the separate lead reference

Every0.2mrad statement above concerns the ORIGINAL four-box reference only. It does not apply to the separately proposed LED/lead reference. Root and critic independently report an exact interior point at1.001999s where that lead reference's hold error exceeds0.2mrad; their final supplement gives the distinct lead-reference allowance11/30000rad. This inventor audit did not derive the lead-reference bound. Importing the original allowance into that changed signal would be invalid even if the command clock and retained history were unchanged.
