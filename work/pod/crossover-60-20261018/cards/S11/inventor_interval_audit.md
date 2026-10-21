# Independent interval audit of PM S11 witness

Read `pm_interval_hold.py`; independently executed its `certificate()` without writing PM files. Independently implemented a direct held-target cell recurrence in `inventor_interval_audit.py`, with **positive-series enclosure of exp(+1/250), inversion, and a different integer scale 10^65**. This does not reuse PM's alternating-series enclosure or six-state matrix. The source coefficients and task data are shared, as they must be for the same claim.

Both exact enclosures overlap at velocity approximately **.0022881462917086763 m/s**, strictly above .001 m/s, after exactly 10.5 seconds beyond arrival. Global time is .3165+10.5=10.8165 s. This is a finite-time witness. It proves neither an infinite periodic limit nor perpetual motion.

## Arithmetic and binding checks

* PM `enc` uses floor for the lower endpoint and negative floor for ceiling; its signed multiplication checks all four endpoint products before outward rounding. Negative fractions therefore round correctly too.
* For x=1/250 the alternating exponential terms decrease. The degree60 even partial sum is above exp(−x); adding degree61 gives a lower bound. Enclosing those endpoints at scale10^60 is valid.
* The first three coordinates are **current physical state relative to c**, and the last three are the one-sample-old state in the same coordinates. Top block `F current − B G previous + B d` and lower identity-copy current are correct. Center offset cancels exactly because the feedback is −8(x−c)−6v−a/2.
* `F12=(1−e)/r`, `F02=h/r−(1−e)/r²` and `B=(h²/2−F02,h−F12,1−e)` are the analytic held-target cell coefficients. No physical state is reset at joins.
* Initial current state is old braking at .3165, previous sample at .316. The delayed command .22264264 agrees with the source's exact first command. Rate8, exact subsequent sensor readings, and .5 ms delay are source-admissible choices.
* Target error is +.01 for 2000 cells and −.01 for 2000 cells, repeating from the first hold cell. It is added **after** the clamp. All exact command intervals lie strictly inside ±2, validating use of the linear recurrence in every cell.
* The default horizon is exactly 21000 cells. The optional duration argument silently truncates non-grid durations while reporting the unrounded requested time. That does not affect the default witness; a reusable consumer needs an integer-grid guard or a residual fractional cell.

## Negative controls and failed attempt

Using the current state instead of the old sample changes the first command and gives a disjoint final velocity interval near .002284339901756169. Clearing the current initial acceleration violates prefix binding and gives a disjoint interval near .0022881462917080436. Both mutations still exceed the coarse .001 threshold: that threshold alone cannot validate that the certificate proves the right execution. The explicit prefix/history checks are essential.

The first independent implementation used the equivalent but uncollected expression `target+e*(a−target)`. Interval dependency accumulated until the clamp-inactivity check failed; this is an enclosure failure, not evidence the true command saturates. The failed script is preserved as `inventor_interval_audit_failed_direct.py`. Collecting the target coefficient into `(1−e)*target` before interval arithmetic removes this artificial dependency; the successful script uses that form.

No full source-execution Lean binding or physical validation was added. The separate arithmetic results and exact sample witness support the next formal acceptance adapter. Critic/root should still reproduce and certify the corresponding source execution rather than accepting algebra by filename.

## Retreat bound improvement record

The initial three-lemma `inventor_retreat.lean` SHA256 was `719e63107baec621dfd1d6b997a7e5b3a66f25aa40540e8c570f5ea38312e767`. Those lemmas remain unchanged.

The critic observed the linear acceleration barrier remains valid after a_bar crosses zero. Evaluating at 2A/K=20/321 s doubles the necessary retreat to **80/103041 m≈.776389981 mm**, the minimum of the integrated cubic upper bound. New named lemmas prove the updated arithmetic and zero upper velocity at that time. The earlier .388 mm result remains valid but weaker.

Root then proposed the stronger exponential comparison `a_bar=B−(A+B)exp(−12s)`. At crossing, `B−a_bar≥0`, so `r(b−a_bar)≤12(B−a_bar)=a_bar'`; this requires no a≥−A premise. Integrating twice at s=1/12 yields `Δx≤B/288−(A+B)exp(−1)/144`. The odd alternating partial through degree7 is greater than367/1000 and belowexp(−1). For A=6/5,B=201/100 this gives **Δx≤−1923/1600000 m =−1.201875 mm**. `inventor_terminal.py` checks the rational partial and arithmetic. A separate Lean lemma checks only the last arithmetic implication, assuming E≥367/1000 and the integrated expression. Full differential comparison, exponential enclosure theorem, and integration are still formalization gaps.

All three bounds are controller-independent **conditional post-first-zero diagnostics** under the stated actuator constraints and residual state. They are not claims about the actual C8 first-zero acceleration or about its literal saved finite witness.
