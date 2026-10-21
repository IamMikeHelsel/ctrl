# S03 supplement: a cell certificate can be an initialization contract

AI-written research contribution. Exact model follows the actual source PD controller,
held acceleration error, energy and step interval; no physical ADC is claimed.

The proposed negative—safe actual execution but a later nearest ADC cell straddling
the invariant boundary—cannot occur under the following declared widened-budget model.
Let E=5x²+2xv+v², initial E≤1/10, h∈[1/20,1/2], and total held acceleration error
|d|≤1/1250. The actual source `Sampling.half_step_contract` gives nominal next energy
at most119/1200. The integrated error is (h²d/2,hd), whose energy is at most29d²/64.
Positive definiteness applied to E(z−1000e) yields

E(z+e) ≤1001E(z)/1000+1001E(e).

Therefore every true next sampled state has energy at most29866837/300000000,
approximately.0995561233. This is a uniform bound, not numerical trajectory sampling.
The interval h lower bound is essential to the contraction used here.

For any nearest-rounding cell of widthδ containing the true state, every cell point
differs from that state by at mostδ per coordinate (half a cell to its center, then
half a cell to the other end). The invariant implies |x|≤.16 and |v|≤.36 by completing
squares. Expanding the quadratic gives a cell energy increase at most84δ/25+8δ².
Thus with decimalδ=.0001 every point in the next cell has energy at most
29967661/300000000, leaving margin32339/300000000≈.000107797.
In particular, the four-corner consumer passes. Convexity of the quadratic also makes
four-corner containment sufficient for the rectangular cell.

The representation transfer is from a repeatedly executed geometric guard to an
initialization precondition plus an inductive execution contract. It preserves the
actual state, energy, controller, step interval and error channel. It does not justify
removing runtime checks for stale samples, failed sensors, wrong conversion, arithmetic
faults or model changes. A repeated checker can still be useful to detect departures
from the contract. No safe fallback is supplied by a rejected guard.

An initial-state negative remains: x=−1/20,v=7/20 has E=.1 and lies exactly on decimal
grid centers, but the cell corner x−.00005,v+.00005 has energy.10002001>.1. Hence a
known safe point and a certified safe ADC cell are different initial assumptions.
The positive later-cell result is a consequence of contraction, not a tautology of
nearest rounding or cell geometry.

## Format and DAC comparison

With physical held error1/4000 reserved and no other arithmetic error, the widened
total1/1250 budget leaves the following maximum absolute output/DAC error:

| Format | Weighted input error | Remaining output/DAC allowance |
|---|---:|---:|
| Decimal scale10000 |1/4000=.00025|3/10000=.0003|
| Q14 |5/32768≈.000152588|8139/20480000≈.000397412|
| Q16 with adequate word widths |5/131072≈.000038147|41931/81920000≈.000511853|

These are error-budget allocations, not measured hardware tolerances. Any other
conversion, computation, output-hold or actuation error spends the same remainder.
Q16's larger allowance does not rescue the explicitly demonstrated narrow-multiply
overflow. The next-cell bound is positive for all three grid widths; JSON records the
exact separate margins. The decimal result applies directly to the root's declared
scale10000 checker only if its accepted cell means this synchronous nearest cell and
its delivered output obeys the channel bound.

Falsifiers for this transfer: allow h→0 (contraction disappears); associate a cell
with a stale state; round with error exceeding half a grid; or change the delivered
error from a pointwise held bound to an average/RMS bound. None is covered by the proof.

Evidence: exact rational Python results in `inventor_readmission.json`; source-importing
Lean helpers in `inventor_readmission.lean` with actual compile log alongside. This
supplement does not itself verify a physical ADC or executable compiler correspondence.
Precise next test: instantiate the conditional margin in the compiled decimal consumer,
including state/sample identity and error-budget inputs; mutate h, age, and cell-width
bindings to ensure the consumer rejects unsupported uses.

Final validation: all five Lean lemmas compile with exit0 using the actual source's
Lean4.35.0 project. Each depends only on propext, Classical.choice and Quot.sound.
Frozen SHA256:74fab9e1e92df9375b5390467b90afde0cffde6157f989a5be1980e1064ab1b9.
The domain researcher independently replayed identical pre/post bytes with exit0;
see `domain_inventor_readmission.log/json`. The critic independently checked the exact
arithmetic and scope. The initial failed compile is retained as
`inventor_readmission_attempt0.lean/log`; it is not accepted evidence. The five helpers
formalize the Young inequality, held-error energy, actual-source nominal endpoint margin,
cell perturbation bound, and final rational margin. Their application to a physical ADC
still requires the declared synchronous cell binding. Python exact replay and Ruff pass.
