# S03 independent critique

The useful contract is a bound on the **delivered held acceleration** relative to the nominal command at the same current true state. It must include ADC, arithmetic, clamp placement, DAC/actuation error and disturbance. A finite-word implementation need not reproduce the source's exact tie rule if it satisfies this generalized bound.

The original Quantized.lean proves mathematical nearest-grid rounding at delta1/10000, clamp after the complete dot product −2x−3v, held acceleration disturbance≤1/4000, and endpoint energy E=5x²+2xv+v²≤.1 for steps h∈[.05,.5]. It is not a machine-word theorem, continuous-time energy theorem, arbitrary time-varying disturbance theorem or hardware certificate. Domain's source-importing interface correctly generalizes the delivered error and carries the actual state/input sequence through induction. The widened total budget.0008 follows a stronger use of the same source contraction; it is a sufficient budget, not an optimal threshold.

## Exact discriminators

Independent critic_exact.py reconstructs the following without producer imports:

- Decimal code(−500,3500) has center(−.05,.35) with E=.1. The strictly interior same-cell point(−1249/25000,8751/25000) has E=7815001/78125000>.1. Center-only energy is therefore unsound; checking all four corners is sufficient because the quadratic is convex. Closed cells are conservative at ties.
- The safe boundary state itself belongs to a cell rejected by the robust cell guard. Rejection is not physical safety: delivering zero for h=.5 yields state(1/8,7/20), E=461/1600>.1. This is a diagnostic alternative policy, not an existing source fallback.
- Truncating positive x=v=.00009 to zero gives control error.00045, exceeding the original.00025 controller budget. Nearest-even and nearest-up differ at ties but both satisfy half-grid error.
- A perfect sample aged.002 in normalized source time at x=0,v=.1 with zero acceleration gives.0004 stale command error at the current true state. This violates the original controller budget; it does not refute the widened.0008 total-error theorem.
- Q16 boundary codes(−3277,22938) correctly produce−62260. Explicit modulo16 intermediate arithmetic produces3276. This is a stated wrap model, not a claim about C signed-overflow behavior. C integer promotions and undefined behavior must be analyzed separately.

Three critic Lean arithmetic lemmas check the center/cell distinction, unsafe zero fallback and stale-error values. Their mapping to ADC/plant semantics remains explicit.

## Actual C replay

critic_decimal.c snapshots root's C bytes. A fresh clang21 build with undefined/signed-overflow sanitizers passes2097 independently checked valid-int16 input cases. An independent integer oracle uses the alternative energy expression4x²+(x+v)². The full finite sweep matches23,071,209 tested codes,15,697,737 robust-cell admissions,15,708,055 center-only admissions,10,318 center-only false-admission cells, and maximum admitted raw magnitude9615. This is finite executable evidence, not a verified compiler/refinement result.

The correct implementation promotes to int64 before quadratic multiplication; signed-int32 raw arithmetic is safe over the declared int16 domain. A modulo32 guard mutation falsely admits code(−32768,−32768): quadratic34360786952 becomes1048584. Assigning an already-overflowed int32 result to int64 would not repair the guard. The executable's scanf interface is tested only on valid bounded integers; arbitrary malformed or out-of-int32 text is not a hardened parser contract. Rejection/control-use logic is outside the arithmetic diagnostic's output format.

Robust energy-cell admission may be required only at initialization if a proved implementation trajectory thereafter maintains true energy inductively. The invariant alone does not establish full-cell acceptance, since safe boundary states can have rejected cells. The later readmission result below supplies the stronger margin for this specific synchronous implementation; initial rejection still needs a separately justified fallback protocol. A diagnostic returning a raw command alongside a rejected flag must not be interpreted as permission to actuate.

## Prior work and scope

The author-hosted [VeriPhy PLDI2018 paper](https://www.cs.cmu.edu/~smitsch/pdf/VeriPhy.pdf) already develops real-to-machine interval semantics and verified controller executables. It explicitly discusses trusted parsing, arithmetic, isolation and physical I/O assumptions. Our bounded arithmetic adapter is not a new end-to-end verified compiler. The relevant transfer is its separation of conservative numerical guards, controller obligations and environment contracts.

GO for a source-bound finite-word/error-budget consumer with explicit initialization and rejected-input behavior. HOLD end-to-end compiled/controller/physical correspondence. NO-GO for center-only admission, unbudgeted truncation/staleness, per-term clipping, or treating rejection as safe stopping. Quality4/4/4/4/2=18/20; subjective confidence high for exact arithmetic, conditional for executable-to-plant refinement.

Independent strengthened overflow witness: Q16 codes(−3277,22872) have every full-cell corner strictly inside E<.1. At the decoded cell center, h=.5,w=0 gives exact endpoint energies973227061/68719476736 for correct wide arithmetic and22364242997/68719476736 for explicit modulo16 output. The latter exceeds.1. Thus the declared wrap model can break the actual endpoint invariant, not merely its sufficient error budget. The imported-source numeric witness uses a nearby same-code true state and is checked separately.

The23m-code C sweep is not all2^32 int16 input pairs. Completeness for admitted codes additionally uses convex-cell containment and the source-derived center projections |x|≤.16,|v|≤.36, placing all admitted centers within |X|≤1600,|V|≤3600. This mathematical coverage bridge is separate from the finite executable test.

## Initialization followed by induction

The clean interface is: (1) a current true-state/ADC half-cell contract and the four-corner initialization guard establish true initial E≤.1; (2) each later sample supplies the same half-cell relation at its own current state; (3) exact integer dot/decoding plus the delivered-error budget establish the source step hypothesis; (4) the actual held-state recurrence supplies the induction step. This avoids imposing a stronger whole-cell admission condition at every safe boundary state. It still requires a theorem relating code to the command actually delivered, correct hold timing and held disturbance, and the physical model. Firmware rejecting bad data is not a proof of physical fallback safety.

Integer decoding is another independent boundary. If an implementation evaluates integer `u_count / SCALE` before conversion, healthy subunit commands decode to zero. For true x=−.05,v=.349, E=99401/1000000<.1, the Q16 proper command count−62062 decodes to0 under that changed rule; h=.5,w=0 then produces E=1144813/4000000>.1. The print-only C experiment does not implement this bug or prove a DAC decoder.

## Stronger readmission margin

The inventor’s later source-specific result answers the repeated-admission concern under stricter explicit premises. Independently, the exact held perturbation has energy≤29D²/64. Source half-step contraction plus the positive-quadratic Young inequality with parameter1000 yields next true E≤29866837/300000000 for totalD≤.0008. A synchronous nearest decimal ADC cell differs from that true state by at most fullδ=.0001 per coordinate; source projections |x|≤.16,|v|≤.36 bound the entire cell by29967661/300000000<.1. Thus every subsequent full cell passes after a valid initial state under these assumptions. This is not valid for stale ADC, changed scaling, extra DAC error or arbitrary hold intervals. Exact arithmetic replay is critic_readmission.json; accepted kernel scope will follow independent compilation.

Time quantities in this card are normalized source units; no conversion to seconds or microseconds is established. An earlier critic message used a physical microsecond label for1/20000; that wording was incorrect and is superseded here.

## Universal word-range obligations

critic_machine.lean proves four universal integer statements over every signed16 input, independently replayed by the domain worker. Raw products and sum stay within±163840, hence signed32 range. Doubled cell coordinates with either corner sign have absolute value≤65537. The actual left-associated quadratic intermediates are bounded individually, culminating at34360786952, within signed64 range. These obligations justify absence of mathematical overflow for the declared expression order and input domain; the C language evaluation, casts, compiler and physical input/output binding remain separate. Failed first-draft tactics and a lexical spacing error were preserved; only the corrected clean exit is accepted.

The later domain decimal contract allows capture age tau≤1/20000 in normalized units, a single retained old acceleration with |b|≤4001/4000, decimal half-cell ADC, DAC error≤.0001, and next held disturbance≤.00025. Its current true E premise is explicit. Same-time full-cell initialization cannot be substituted for this current-state premise when the cell was captured earlier. A propagated initial uncertainty certificate or justified prior history is still required. The synchronous readmission result remains a separately typed positive contract.

Independent acceptance at checkpoint:47 declarations accepted, with final root initialization theorem awaiting the domain worker’s private replay. Source decimal5 and root encoding4 freshly replayed; source dependencies rebuilt privately for the composed decimal module. Inventor readmission5 independently compiled by the domain worker, with receipts and stable hashes inspected by critic plus an independent rational derivation. No false or failed draft is counted.

Final S03 acceptance:48 unique declarations, pending0. The last initializer was independently compiled by the domain worker with private rebuilt PM dependencies; critic inspected its source, hashes and axiom receipts. All permitted axioms only, with three axiom-free BitVec checks. The final CARD scope audit passes.
