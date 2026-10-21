# C10 domain review

AI-assisted domain researcher, inherited root model; exact model identifier unavailable. Root owns session timestamps and the PM gate. Original sources and other campaign cards are unchanged.

The frozen question is whether finite-horizon bounds can certify the same short move where the global invariant cube is excessively conservative. The source comparison is `research/adjacent-controls/tracking-replans/comparison.py`, next to the roster-linked README under `/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/`. The other roster source, `research/pods/2026-10-17/controls/filter-enclosure-08/builder/report.txt`, supplies a useful exact Taylor-enclosure technique, but its filtered fourth-order plant is NOT substituted for the tracking comparison plant.

## Exact recovered task and strongest prior result

The source short_high_jerk move uses jerk(+10,-10,-10,+10)m/s³ for four phases each1/50s, then4s hold. It begins from zero physical and reference states, ends the motion at1/6250m=.16mm with zero reference velocity/acceleration, and preserves the physical state through every join. The sigma1 plant is x'=v,v'=a,a'=r(u+w-a), with r∈[8,12]. All three saved laws have acceleration feedforward and feedback(-8e_x,-6e_v,-e_a/2); jerk coefficients are0,1/10,5/48. The saved disturbance is−(1−exp(−20t))/2000, bounded byW1/2000.

The checked invariant-cube result covers every admitted varying rate and bounded disturbance, conditional on trajectory existence and its stated regularity. Its sufficient radii for the three laws are2501/4000m,501/4000m,1253/12000m. Saved simulations are only sampled evidence. The especially bad varying-rate short-move midpoint result is about1.96mm; therefore improving the proof cannot make that same robust0.2mm claim true. Root's separate switched-rate counterexamples further address this obstruction.

## Exact continuous finite-horizon test

`domain_enclose.py` uses the unchanged direct controller and reference, with each of the three saved fixed rates8,10,12. The augmented state is(e_x,e_v,e_a,exp(−20t),1), with the exact phase matrix

```
e_x' = e_v
e_v' = e_a
e_a' = -8r e_x -6r e_v -(3r/2)e_a + (r/2000) exp(-20t)
         + (r*kappa-1)*j-r/2000
exp(-20t)' = -20 exp(-20t)
1' = 0.
```

All five states carry through all408 cells of length1/100s. Only the phase's jerk coefficient changes; no physical, error, exponential, or filter state resets. Integer intervals at scale10^100 round every rational multiplication outward. For M=dt*A, a=||M||infinity, and B bounding the incoming vector, the omitted Taylor series after degreeN is bounded by

`B*a^(N+1)/(N+1)! / (1-a/(N+2))`.

The code requires the exact bound below10^-80 and pads every component. To cover EVERY time in a cell, each finite-series term is multiplied by an independent theta^n∈[0,1]; consequently the interval hull adds[min(0,term_lo),max(0,term_hi)]. This loses correlation but is an inclusion, not sampled acceptance. The same tail bound covers every smaller time. Phase endpoint enclosures transfer into the next cell. Up to70 terms suffice.

All nine cases satisfy the0.2mm threshold throughout the full4.08s horizon. Worst continuous upper bounds over the three FIXED rates:

| Jerk coefficient | Exact upper bound, m | Approximate mm |
|---|---:|---:|
|0|2994109/25000000000|0.11976436|
|1/10|62544009/1000000000000|0.062544009|
|5/48|6254229/100000000000|0.06254229|

These results retain the original source disturbance waveform. They do NOT certify the interval of constant rates, arbitrary varying rates, or arbitrary bounded disturbances. `domain_enclose.json` records the matrices' parameters, every continuous cell tube, endpoint summaries and tail metadata; the script recomputes all fine-grid intervals deterministically. JSON endpoints are coarsened outward for readability. The method is exact executable arithmetic plus a mathematical Taylor/ODE justification, not a Lean-certified ODE solution.

## A stronger source-faithful slice: arbitrary disturbance at r=8

At fixed r=8 the error denominator is exactly(D+4)^3. Its causal impulse response is h(t)=t²exp(−4t)/2 for t≥0. Write alpha=8*kappa−1. For zero initial error,

`e = alpha*(h*j) + 8*(h*w)`.

The source reference velocity g=q' is nonnegative. On local time s∈[0,h0], its four phases are

```
J*s²/2,
J*(h0²/2+h0*s-s²/2),
J*(h0²-s²/2),
J*(h0-s)²/2.
```

Their integrals sum toD=2J*h0³=1/6250. Velocity and acceleration are continuous at all joins, and both start at zero. Two integrations by parts therefore give h*j=h''*g, without an impulsive phase-boundary term. This is precisely where retaining the reference history matters.

For t≥0, `h''(t)=(1−8t+8t²)exp(−4t)` has absolute value≤1. Set x=4t; the exponential lower bound1+x+x²/2 proves both sides of `|1−2x+x²/2|≤exp(x)`: the upper difference is3x, and the lower difference isx²−x+2>0. Moreover h≥0 and8∫h=1/8. Thus, for arbitrary locally integrable disturbance |w(t)|≤W,

`|e(t)| ≤ |8*kappa−1|*D + W/8` for every t≥0.

For the unchanged short move and W1/2000, midpoint gives107/1200000m=.0891667mm, nominal gives189/2000000m=.0945mm. Both certify0.2mm for all time on this fixed-r8 slice. For zero jerk feedforward the same simple bound gives.2225mm and does NOT certify the threshold. This failure is retained; no coefficient is silently changed.

`domain_kernel.lean` checks the exponential polynomial inequality, actual h'' bound, source polynomial velocity nonnegativity, algebraic sum of the four antiderivative evaluations, and exact two budgets. The full convolution/ODE identity, integration-by-parts bridge, and integral bound remain the written derivation above. The antiderivative lemma is algebraic, not a formal interval-integral theorem. Do not describe the resulting physical/error bound as fully kernel-proved. An initial compile failed due to an absolute-value token spacing syntax issue in the two budget statements; corrected source is replayed separately, with axiom output in its log.

## Interpretation and next action

Crossovers: validated reachability provides continuous finite-time tubes; positive impulse responses provide disturbance L1 gain; total variation of the monotone reference velocity preserves cancellations lost by a jerk-amplitude invariant cube. Each preserves the source dynamics and initial/history semantics while exposing its exact uncertainty quantifiers.

The fixed-rate tests and r8 analytical slice give a defensible path to narrower certified operating contracts. They cannot rescue an unrestricted varying-rate0.2mm claim contradicted by admissible witnesses. Recommended PM split: GO for explicitly admitted rate classes and certificate tooling; NO-GO for replacing a failed full-band claim with a sampled/fixed-rate pass. Next test: independently bind the r8 convolution derivation to the source error ODE, and determine a quantitative rate-variation admission budget before trying to extend the fixed-rate certificate.

Quality rubric: faithfulness4/4, reproducibility4/4, discriminatory value4/4, critique3/4, actionability4/4 =19/20 (95%). This is a quality assessment, not a success probability. Subjective confidence in the stated exact arithmetic and scope:95%, pending independent replay. No hardware or full repository integration claim.

Reproduction:

```
uv run --no-project --python /usr/local/bin/python3 python work/pod/crossover-60-20261018/cards/C10/domain_enclose.py
cd lean
lake env lean ../work/pod/crossover-60-20261018/cards/C10/domain_kernel.lean
```

Read-only implementation source hashes: comparison.py `9b31c263ec5a1feaf68683d1e40ee24bf2e0146c160662c5537404c12dfdbf6e`; original filter enclose.py `98db00af4382e297cb821e7130ba9b23df469818e5bf9411b5520c9ec4226a29`. Final domain Python Ruff check and format pass. These isolated campaign artifacts do not change production code; no full repository-check claim is made.
