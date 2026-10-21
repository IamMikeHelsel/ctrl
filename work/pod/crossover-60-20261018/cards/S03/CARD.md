# S03 — Machine arithmetic to real-valued control theorem

**PM: GO, quality95/100 (19/20).** AI-written initial review with root PM, domain researcher, inventor and independent critic. Actual substantive durations are in state.json; conservative context gap excluded. All four roles used the inherited working model; exact runtime model ID unavailable. No alternate-model or Spark inference claimed.

Question: What error contract lets a finite-word implementation inherit the real-valued clipped controller guarantee, including overflow and rounding?

## Provenance and strongest prior result

Original investigated source proves ideal nearest rounding over mathematical reals and explicitly excludes executable correspondence. Nominal normalized double integrator: E=5x²+2xv+v²≤.1, feedback−2x−3v, global clamp±1, quantizerδ=.0001, actual holdh∈[.05,.5], heldphysicalerror≤.00025. It guarantees sampled endpoint energy. This is not the third-order industrial lag model, an intersample guarantee or robot validation.

- /Users/mike/Dev/ctrl-research-notebook/research-notebook/lean-controls/README.txt
- /Users/mike/Dev/ctrl-research-notebook/research-notebook/lean-controls/LeanControls/Quantized.lean
- /Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/adjacency-review/safety-filter-review.txt

Frozen source hashes are unchanged; resources/s03-source-preservation.json records checks. Six imported source dependency files were independently hashmatched to the historical cache; new wrappers were freshly compiled, not a fresh dependency closure build.

## Transfers, assumptions and tests

1. **Numerical error budgets → compiler/control refinement.** A delivered-command error contract preserves the actual state recurrence and exact global clamp. Source contraction supports total error.0008, exceeding its original sufficient.0005 allocation. Exact decimal halfcells consume.00025; physical disturbance consumes.00025. The remaining.0003 can pay for declared arithmetic, age and DAC errors. Domain's source-imported joint theorem allows normalized age≤1/20000 within one retained constant-acceleration hold, old|b|≤1.00025, DACerror≤.0001, exact dot, and currentE≤.1. It proves nextE≤.1 and|u|≤1. Capture-time admission does not initialize currentE without propagation. Across-hold integral generalization remains hand mathematics.
2. **Ellipsoid support → word-range design.** Exact4u0²+(13x+v)²=37E gives tight support and conservative range bounds. Q14 admits16-bit products/sum under declared bounds; Q16 requires wider arithmetic/output despite16-bit input codes. Explicit modulo16 negative at x−.05,v.349 is inside a wholly admitted cell, yet wrong command+3474/65536 yields nextE≈.32545 at legalh=.5; correct−62062/65536 yields≈.01416. Source-bound Lean inequalities and independent exact replays confirm failure. This is declared BitVec/modulo semantics, not an assertion about unspecified C signed overflow.
3. **Set-valued sensing → exact cell admission.** Four integer quadratic corner checks plus convexity establish true initialization for a same-time halfcell contract. Local-quadratic initializer and actualsourceE have a reviewed ring-identity bridge; no silent name substitution. Root C uses int32 whole dot and int64 energy intermediates. Fresh23,071,209-case sweep and independent sanitized replay agree:15,697,737 admitted cells;10,318 center-only ambiguous cells; peakraw9615. Root36,679-case exact oracle independently replayed. Universal integer range lemmas supplement finite cases; compiler, parser and physical decoding remain separate obligations.
4. **Unexpected transfer: noise shaping → dynamics-weighted moments.** Opposite held errors sum tozero but leave nonzero state. Average/RMS bounds cannot replace the pointwise source channel. Clamping individual products also destroys cancellation. Both failures identify what a valid mapping must preserve.

## Independent challenge and positive refinement

Center-only admission, explicit energy wrap, wrong word width, per-term saturation, stale samples, truncation, premature integer division and zero-command rejection fallback all have precise counterexamples or error-budget failures. They are not all equivalent safety counterexamples; role reports distinguish them.

A stronger synchronous result survives critique: exact held-error energy≤29D²/64 and a Young inequality yield endpointE≤29866837/300000000 atD=.0008. Any fresh decimal cell corner adds at most.00033608, so the entire next cell hasE≤29967661/300000000<.1. Five source-imported lemmas independently replayed; the final ADC-cell/recurrence composition is reviewed mathematics. This supports recurring re-admission under compliant synchronous updates. It does not supply an initial rejection fallback, stale-cell guarantee or fault recovery.

Acceptance detail: critic_acceptance.json is the authoritative independently replayed declaration ledger. Pending, failed, or sorryAx-bearing drafts are excluded. Standard permitted axioms only; three concrete BitVec checks are axiom-free. Logs preserve failed cancellation/parser/build-root attempts and successful repairs. NativeC and Python results are exact executable experiments, not verified compilation. Source binding, kernel lemmas, hand composition, novelty and physical validation remain separate.

## PM decision and next action

GO for the named refinement route; NO-GO for the tested overflow/termwise-clamp/center-only/fallback shortcuts. After all60 initial reviews, run the30-minute consumer experiment in next_block_protocol.json: bind source/format/compiler/decoder/ADC/age/hold/DAC manifests, reproduce valid traces, and reject20 semantic mutations. Give every GO its first block before renewal. Full executable and hardware assurance HOLD on those named interfaces.

Quality rubric: faithfulness4/4, reproducibility4/4, discriminating tests4/4, independent critique4/4, actionability3/4=19/20. Subjective confidence high in accepted exact/kernel claims; practical utility and physical safety are uncalibrated. [VeriPhy2018](https://www.cs.cmu.edu/~smitsch/pdf/VeriPhy.pdf) already demonstrates the generic real-to-machine refinement route; no novelty claim for that methodology.
