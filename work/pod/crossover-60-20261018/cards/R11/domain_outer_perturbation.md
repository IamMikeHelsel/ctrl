# Retained outer-ramp perturbation audit

AI-authored independent derivation, requested after the initial domain report. This note changes no shared files and does not claim a complete interconnected stability proof.

## Exact retained-history recurrence

Read root `pm_ramp.py/json`: visual period H=1/50s, gain K=10/s, κ=KH=1/5. During interval k, the reference velocity ramps linearly from retained `v_(k−1)` to newly computed `v_k`. Let the target g be constant, x_k=r_k−g, and the actual visual observation be

    y_k = r_k + η_k,   η_k = e_k+n_k,

where e_k=θ_k−r_k is physical inner tracking error and n_k is additive visual measurement error. The exact delayed feedback law is

    v_k = −K*(y_(k−1)−g) = −K*(x_(k−1)+η_(k−1)).

Retaining the OLD velocity, rather than resetting it, yields

    x_(k+1) = x_k + H*(v_(k−1)+v_k)/2
            = x_k − (κ/2)*(x_(k−1)+x_(k−2))
                  − (κ/2)*(η_(k−1)+η_(k−2)).

Thus the root's nominal three-state matrix is correct when η=0. With η≠0, its first state equation has the explicit extra input `−(η_(k−1)+η_(k−2))/10`. It cannot be discarded merely because the inner controller has a small tracking tube. Initial x, η and velocity histories must be consistent with the same accepted task and retained samples.

A more informative coordinate is the measured target error z_k=y_k−g=x_k+η_k. Exact substitution gives

    z_(k+1) = z_k − (z_(k−1)+z_(k−2))/10 + (η_(k+1)−η_k).

Consequently the nominal Lyapunov matrix P can be used in these shifted coordinates only with the added first-difference forcing. A bound on |η| is not a bound on |η_(k+1)−η_k| strong enough to recover the root's nominal acceleration certificate automatically. If the target varies and each retained command uses the target stamped with its observation, the equation additionally contains `−(g_(k+1)−g_k)`; changing target semantics requires a separate rederivation.

## Constant η: three distinct outputs

For η_k=η0 constant, the equilibrium is x*=−η0, so

    reference r*=g−η0,
    measured visual y*=g,
    actual optical θ*=r*+e0 = g−n0   if η0=e0+n0.

The shifted history z=x+η0 follows the root's homogeneous matrix exactly. Therefore a constant INNER tracking offset e0 alone can be cancelled by the outer controller at steady state, although the reference is offset from the target. A constant VISUAL sensor bias n0 remains in the actual output. A measured visual residual of zero therefore does not establish actual world-target alignment.

These are conditional steady-state identities. A nominal homogeneous stability proof in z establishes convergence only after its shifted initial state and constant-η assumptions are admitted. It does not establish that the interconnected inner error becomes constant. In particular, periodic inner error sampled at a fixed phase can look constant at visual sample times while retaining an intersample output ripple.

The root's initial nominal history x=(1/10000,1/10000,1/10000) must be shifted by η0 before applying P. For η0=23/5000, the z history is (47/10000) in each coordinate. Its P-energy is2209 times the original energy, namely69179253/316000000000. The old small initial-energy admission is no longer justified. This is a failure of reusing that particular sufficient certificate, not evidence that this constant-bias trajectory violates speed or acceleration limits.

## Exact level-only composition counterexample

The reference ramp has acceleration

    rddot = (v_k−v_(k−1))/H
           = −(K/H)*(z_(k−1)−z_(k−2)).

Take x_k=0 at every sample and η_k alternating between ±E, E=23/5000rad. This sequence satisfies the perturbed sampled recurrence because successive η values sum to zero. Nevertheless the retained velocity alternates between ±K E=±23/500rad/s. Each continuous ramp has acceleration magnitude

    2*K*E/H = 23/5 rad/s² = 4.6 rad/s²,

which exceeds the inner theorem's assumed reference acceleration bound1rad/s², even though its reference speed remains below0.1rad/s. The within-interval reference displacement reaches K E H/4=23/100000rad before returning to its sampled value0. Checking only sample positions would miss both facts.

This is an exact counterexample to composing the outer law using ONLY the scalar bound |η|≤4.6mrad. It is NOT asserted to be a trajectory of the full inner actuator/error ODE under the source's allowed disturbances. That stronger realization would need a coupled construction. Its legitimate conclusion is narrower: the magnitude-only interface loses information needed to infer the required acceleration admission. A slope/increment envelope for η, or an independently governed outer acceleration, is needed.

## Next proof obligation

Use the actual inner model to bound η increments (including visual measurement dynamics), then derive a forced P inequality for z. Prove that its invariant domain implies both |Kz|≤0.1 and |K(z_prev−z_prevprev)/H|≤1. Alternatively govern the outer acceleration explicitly and rederive its retained-state recurrence; do not keep the old matrix after modifying the law. Finally transfer the outer bound to actual θ using the separate sensor/inner-error identity. This note is algebraic/manual evidence, not new kernel declarations or physical validation.

## A sufficient but strong increment contract

Condition on the root's exact P certificate `P−AᵀPA=I`, with `I/2≤P≤20I`, and write the shifted recurrence as z_next=A z+b u, b=(1,0,0), u=η_(k+1)−η_k. Independent multiplication gives

    C=bᵀPA=(1515/158,−165/79,−357/316),
    P11+2||C||²=10308009/49928<207.

Cauchy–Schwarz and Young give `2u C z ≤ ||z||²/2+2||C||²u²`. Therefore

    E_next ≤ (39/40) E + 207 u².

If initially E≤1/2000000 and every increment satisfies |u|≤1/200000rad (5 microradians per20ms), this energy cap is invariant: substituting the cap and increment bound yields a strict margin. The lower spectral bound gives ||z||≤0.001, whence ramp speed≤0.01rad/s and acceleration≤1rad/s². This is a sufficient conditional admission interface, not a bound derived from the actual inner servo/sensor channels. Past observed small increments do not guarantee future increments under arbitrary disturbances.

`domain_increment.lean` checks the exact Young coefficient, scalar budget arithmetic and one-step scalar energy-cap implication. The multidimensional P/Young derivation, complete recurrence induction and physical η-increment bound are not claimed formalized by this small module. In particular, one cannot replace the strong increment premise by the earlier4.6mrad amplitude bound.

## Independent aggregate-countermodel audit

An initial critic script used only two reference histories and therefore had one less sample of delay than root's three-state ramp. Promotion was held and that draft was preserved by its owner. The corrected script uses three histories and the matching eta indices. This role independently reconstructed its recurrence with70-digit Decimal arithmetic from the saved forcing schedule, without importing producer functions, corroborating peak actual error0.0066670247134227377rad at step107, ramp acceleration below0.922374rad/s² and speed below0.066671rad/s. This is numerical corroboration of the corrected recurrence; the critic/root own exact directed-interval certification.

The forcing model is `eta_dot=−40eta+f`, |f|≤0.184, with |eta|≤0.0046. The result shows that this aggregate inner-error contract plus the nominal ramp does not imply a5mrad actual target bound, even while the ramp's admitted rate/acceleration limits hold. It is not asserted to realize the particular correlated timing/sensor disturbances of the original executor. This reinforces the need for a full interconnection contract instead of adding separately valid headline bounds.

Local kernel supplement status: all three `domain_increment.lean` declarations compile with only standard allowed axioms. Independent replay is requested.
