# S03 inventor — lattice exactness requires a word-range contract

AI-written inventor contribution; inherited root model, exact identifier unavailable.
Read the actual Quantized.lean, SampledPD.control, PD.energy and the original adjacency
review. Source control is u=-2x-3v, energy E=5x²+2xv+v², safe endpoint region E≤.1,
held step h∈[.05,.5], ideal quantizer delta=.0001, clip limit1, and held physical error
|w|≤.00025. The source explicitly excludes machine arithmetic/executable correspondence.
Its generic useful channel is delivered-command error plus physical error≤.0005.
The domain owns a source-bound version of that channel theorem.

## Three transfers, with preserved invariants and falsifiers

1. **Integer-lattice compilation and resource allocation.** Coefficients2,3 are exact
integers. With a common fixed-point scale, -2X-3V has no arithmetic rounding if every
operation is represented exactly and overflow is excluded. This lets the proof budget
separate input conversion, accumulator range, final clipping, and output/DAC conversion.
More fractional bits reduce input error but consume range. The Q14/Q16 comparison below
makes that tradeoff concrete. Falsifier: show only that input codes fit in their words,
then silently multiply or accumulate in the same width. The admissible Q16 example fails.
These are declared alternative formats, not exact implementations of decimal quantize.

2. **Compiler rewrite validity under saturation.** Linear arithmetic permits reassociation
and cancellation only while the machine operations implement that arithmetic. A saturating
operation is nonlinear; it cannot be distributed over terms. At x=-.05,v=.35, E=.1,
source clamp(-2x-3v)=-.95. Clamp(-2x)+clamp(-3v)=-.9, a .05 difference, far beyond the
.00025 controller-error allowance. Final clipping cannot recover the removed cancellation.
Falsifier: optimize an accumulator by saturating each multiply separately and claim the
source clamp theorem applies. The root's declared wide-dot-then-clamp implementation
avoids this rewrite; this diagnostic is not an assertion of a bug in existing source code.

3. **Unexpected transfer: moment accounting for noise-shaped error.** A residual accumulator
or zero-average quantization error may cancel a sum while leaving the plant state changed.
With the actual sampled PD law, h=.5, initial rest, and held command errors +e,-e, exact
integration gives final x=e/32 and v=-7e/8. At e=.00025 both errors individually satisfy
the allowed channel, and commands remain inside actuator limits, but the final state is
not the ideal rest trajectory. This is not a safety failure; it refutes exact cancellation
from an average-error claim. A future noise-shaping scheme needs an augmented state/error
invariant and the right dynamics-weighted moments. It cannot replace the current pointwise
contract by a mean or RMS claim. These held errors are a declared diagnostic sequence,
not claimed outputs of nearest rounding at an initial zero state.

## Fixed-format calculation and overflow controls

`inventor_words.py/json` uses exact rational arithmetic and an explicitly declared
nearest/ties-to-even converter. Its conversion is a mathematical executable model, not a
hardware ADC model or a claim of matching Lean's tie convention. Only the half-grid error
bound is used. Completing squares gives E=(v+x)²+4x² and 5E=(5x+v)²+4v², hence the
conservative projections |x|≤.159, |v|≤.354 throughout the source region.

| Format | Conservative input-code bounds | Dot bound | Weighted input error |
|---|---|---:|---:|
| Q14, scale16384 | abs(X)≤2606, abs(V)≤5801 |22615|5/32768≈.000152588|
| Q16, scale65536 | abs(X)≤10421, abs(V)≤23201 |90445|5/131072≈.000038147|

Both input pairs fit signed16. Q14 products, sum and limit±16384 fit signed16 as well.
Q16 needs a wider accumulator and output: its limit±65536 itself does not fit signed16.
Signed32 easily contains these declared bounds. These code boxes prove arithmetic range,
not state admission; accepting their entire rectangle would not establish E≤.1.
An input-cell energy check must retain the unknown true state, as in the root's separate
four-corner admission gate.

Boundary negative: x=-1/20,v=7/20 lies exactly at E=.1. Q16 codes X=-3277,V=22938 fit
signed16, while 3V=68814 does not. Under explicitly declared modulo16 multiplication,
3V becomes3278; a wide subsequent sum/clamp gives3276 instead of the correct-62260.
The normalized delivered-command difference is exactly1. The wrong command is positive.
This is a BitVec/modulo diagnostic, not a claim that C signed overflow has wrap semantics
or that a C int16 operand necessarily multiplies in16 bits; C promotions and the actual
compiler expression must be bound independently.

A strict-interior version avoids relying on a boundary cell: x=-.05,v=.349 yields
X=-3277,V=22872. Every one of the four half-LSB cell corners has E<.1. Correct output
is-62062; the same wrapping-product error gives+3474, again a normalized difference1.
A valid input-cell certificate therefore does not repair an incorrect accumulator width.

The remaining controller-error allowance after input conversion is positive for either
format, but it must pay for any additional ADC, arithmetic or DAC errors. The physical
held-error .00025 is already reserved separately. No finite-word format establishes that
physical sensing or actuation satisfies those residual bounds.

## Evidence and next action

The exact script passes both formats, boundary/interior overflow negatives, clamp-order
negative, and the zero-sum-error diagnostic. `inventor_words.lean` contains small scalar,
integer and BitVec lemmas; its adjacent log records actual compile status. These lemmas
are not a verified C compiler or an end-to-end deployed executable proof.

GO: compose the domain's actual-source delivered-command theorem with a declared format,
checked input cell, explicit operation order, non-overflow proof and output error budget;
then independently compare the concrete compiled implementation against that specification.
Reject wrong widths, per-term clipping, cell-center-only admission, and undeclared tie or
DAC semantics. Rejection does not provide a safe fallback automatically. Hardware residual
assessment and a deployed implementation theorem remain HOLD on those named interfaces.
Quality18/20 (faithfulness4,reproducibility4,discrimination4,critique3,actionability3).
Subjective confidence98% in isolated exact arithmetic, no physical validation claim.


Final kernel status: nine lemmas compiled successfully. The three concrete BitVec lemmas
use no axioms; the six other lemmas use only propext, Classical.choice, Quot.sound.
Frozen SHA256: 151d28de7b5d48257e1ecfcf94937e0876065b6a0cbe503ec09c5ed227da5572.
The explicit BitVec semantics establish the modulo counterexample; they intentionally do
not assert an unspecified C expression evaluates in that width. Python exact replay and
Ruff checks pass. Independent critic replay was requested on the frozen artifacts.

## Resumed-session result: induction replaces repeated geometric admission

The supplementary `inventor_readmission.md` records a stronger, source-specific result.
Using the widened total held-error budget .0008 and the source half-step contraction,
every later decimal nearest ADC cell lies strictly within E≤.1; exact residual margin
is32339/300000000. Q14 and adequately widened Q16 also pass. This means the full-cell
check can serve as initialization, with subsequent containment following from the
execution contract. It does not eliminate the need to detect broken timing, stale data,
conversion faults or changed error budgets. A safe initial point can still fail its
full-cell check; x=−.05,v=.35 is an exact example. Independent critic arithmetic agrees.
The associated source-import Lean helpers and compile logs distinguish producer checks
from independent replay. Output/DAC allowances after input and physical-error reservation
are decimal .0003, Q14 approximately .000397412 and Q16 approximately .000511853.
These are mathematical budgets, not measurements of a hardware interface.
