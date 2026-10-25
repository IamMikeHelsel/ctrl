# Next experiment: spend clearance margin where it matters

2026-10-21 · AI-assisted analysis and planning; no new safety proof.

The current one-dimensional model suggests testing timestamp-to-braking integration before
expanding robot complexity. Its exact formula permits a useful sensitivity comparison without
claiming that a faster controller or better sensor has been built.

## Sensitivity at an explicit baseline

For position error `e_p`, estimated speed `v`, speed error `e_v`, total delay `tau`, maximum
forward acceleration `A`, and guaranteed braking magnitude `b > 0`, write

`u = v + e_v`, `w = u + A*tau`,

`R = e_p + u*tau + A*tau²/2 + w²/(2*b)`.

Keep the existing stationary-wall, forward-motion and held-rest assumptions. Each derivative
holds the other inputs fixed; feasible engineering changes may couple them.

| Input | Partial derivative of required clearance `R` | Units |
| --- | --- | --- |
| Delay `tau` | `w*(1 + A/b)` | m/s |
| Speed-error bound `e_v` | `tau + w/b` | s |
| Position-error bound `e_p` | `1` | m/m |
| Guaranteed braking `b` | `-w²/(2*b²)` | s² |

Use the existing illustrative baseline: `v=1 m/s`, `e_v=0.1 m/s`, `e_p=0.02 m`,
`tau=0.20 s`, `A=1 m/s²`, `b=2 m/s²`. These are mobile-robot-scale example values,
not measured specifications. Then `R=273/400 m = 0.6825 m`, and the derivatives are
respectively `1.95 m/s`, `0.85 s`, `1`, and `-0.21125 s²`.

The following changes use the **exact finite differences**, not a derivative approximation:

| Hypothetical improvement, others fixed | Clearance saved |
| --- | ---: |
| Delay reduced by 20 ms | `387/10000 m = 38.7 mm` |
| Speed-error bound reduced by 0.02 m/s | `169/10000 m = 16.9 mm` |
| Position-error bound reduced by 0.01 m | `1/100 m = 10 mm` |
| Both sensing improvements above | `269/10000 m = 26.9 mm` |
| Guaranteed braking increased from 2 to 2.2 m/s² | `169/4400 m ≈ 38.41 mm` |

Here a 20 ms delay reduction saves more clearance than both specified sensing improvements.
The exact crossover lies between 13 ms (25.22325 mm saved) and 14 ms (27.153 mm saved).
For a delay reduction `d`, the exact saving is
`w*(1+A/b)*d - A*(1+A/b)*d²/2`. For a speed-error reduction `q`, it is
`(tau+w/b)*q - q²/(2*b)`. These require `0 <= d <= tau` and `0 <= q <= e_v`.

This is a comparison of specified changes, not an unconstrained optimum or an effort/cost
ranking. Collect implementation cost and credible achievable bound reductions before allocating
engineering time. Increasing an assumed braking number without new evidence is not improvement.

## Practical integration with the existing TimingSink

`experiments/timing_contract.py` returns a position center, radius and maximum age at the queried
execution time. It does **not** yet return a velocity enclosure, command validity token, or
braking guarantee. Build an offline adapter first, with no actuator output:

1. Map acquisition intervals into the same monotonic clock epoch as decision time `t_d`.
   Query `TimingSink.at(t_d)`; carry its accepted sequence and epoch separately. Expired,
   missing, future-ambiguous or wrong-epoch state must produce an unsupported verdict.
2. Use the returned position center and radius at `t_d`. Add a velocity enclosure from the
   observation: with `H=t_d-capture_lo`, a conservative interval is
   `[v_obs-e_v-A_age*H, v_obs+e_v+A_age*H]`. This needs the supplied absolute acceleration bound.
   If the interval crosses the backward-motion regime, flag the existing model as unsupported
   until a signed-velocity extension is reviewed.
3. Define future delay once: `tau_future = latest_guaranteed_braking_onset - t_d`, including
   remaining compute, queue, transport and actuator reaction. **Do not add acquisition age
   again:** it is already included in the propagated position and velocity bounds. Conversely,
   using raw capture-time state requires the complete capture-to-braking delay.
4. Immediately before application, requery and check epoch, sequence, deadline and bound
   identity. Existing immutable predictions are not revoked by a later reset. An unsupported
   verdict requires a separately validated supervisor; rejection itself does not brake a robot.

For exact timestamps, the two time conventions must agree when their bounds match. Splitting
the baseline delay into age `3/25 s` and future delay `2/25 s`, propagating upper position by
`u*H+A*H²/2` and upper speed by `A*H`, gives exactly `273/400 m` again. Interval timestamps can
add conservatism, so require enclosure rather than equality in that case.

## Falsifiable checks before a broader claim

- **Timing composition:** replay variable arrival delays, overlapping acquisition intervals,
  blackout, reorder and resets. Compare raw-capture and propagated-state conventions against
  independently integrated trajectories. Any admitted within-contract wall crossing fails.
  Explicitly mutate the adapter to omit age and confirm the test exposes a false admission;
  adding age twice should expose unnecessary conservatism.
- **Numerical refinement:** retain `Fraction` as an oracle. A later float implementation needs
  a verified outward enclosure, not a tolerance that silently accepts near-boundary violations.
  Exercise exact boundary neighbours, conversion from integer timestamps, cancellation,
  overflow, subnormal values and nonfinite inputs. An interval verdict straddling the threshold
  is unsupported. Agreement on samples is testing evidence, not a refinement proof.
- **Unknown braking:** require an evidenced strictly positive lower bound with operating
  conditions and validity interval. Unknown, zero, stale or out-of-domain braking is unsupported.
  As a negative control, keeping the baseline inputs but using actual `b=1.5 m/s²` gives
  `247/300 m ≈ 0.82333 m`; a wall at `0.70 m` is admitted under declared `b=2` and then crossed.
  This diagnoses an invalid bound, not a contradiction of the conditional calculation.

Log minimum clearance, false admissions, unsupported decisions, excess conservatism, clock
resets, deadline misses and bound violations separately. The first useful contribution would
be a reproducible timestamp/uncertainty/braking composition with counterexamples and explicit
contracts. Stopping algebra and its derivatives are known. A new theorem or method would need
a materially new statement, literature comparison and independent validation; none is claimed.

All listed fractions and finite differences were checked with `uv run python` using
`fractions.Fraction`, including the two delay conventions and weaker-brake counterexample.
The derivative formulas were derived algebraically; this note adds no Lean theorem.

Suggested site sentence: “In one specified model, removing 20 ms of delay saves 38.7 mm of
required clearance; the next experiment checks whether timestamp and actuator bounds can
support that calculation in an integrated loop.”
