# S03 root PM research notes

AI-written, inherited root model; exact runtime model ID unavailable. Four roles reused; no Spark inference or alternate authenticated model used in this session.

## Source question and success criterion

An error contract must connect actual finite-word input/operation/output semantics to the unchanged real-valued clipped controller and its true-state recurrence. Original model: normalized double integrator, E=5x²+2xv+v²≤.1, u0=−2x−3v, h∈[.05,.5], held physical disturbance≤.00025. This is sampled endpoint safety, not intersample/physical robot validation. C11 and other third-order lag results are not substituted.

## Root experiment and independent controls

The decimal experiment stores valid signed16 codes at scale10000, evaluates the entire dot product in int32 before final clipping, and computes each four-corner cell quadratic in int64, widening operands before multiplication. Output counts are mathematical data, not a DAC implementation. The valid-code input precondition excludes arbitrary unbounded text; scanf parsing is not hardened. No public CLI change.

Fresh C sweep tests23,071,209 code pairs, admits15,697,737 robust cells vs15,708,055 center-only pairs (10,318 ambiguous). Peak admitted raw command9615; clipping inactive. The scan rectangle covers all admitted cells by convexity/center projection, not by enumerating all2^32 signed16pairs. Independent UBSan-compiled snapshot reproduces the sweep and2097 code cases. Root Python big-integer oracle tests36,679 boundary/fullword cases, finding9056 center-only cases and2337 explicitly simulated wrapped-int32 energy false admissions. These counts are case-set specific. Native compiler trusted; no machine-code semantics theorem.

Explicit bad operations are discriminating tests: modulo16 products can reverse the command and violate endpoint energy from an admitted cell; per-term saturation breaks cancellation; center-only energy admits unsafe states; zero-command rejection fallback can violate safety; premature integer division destroys subunit command decoding. Declared wrap semantics are not claimed to be unspecified C signed-overflow semantics.

Root formal pieces: pm_cell convex-quadratic interval and rectangle lemmas; pm_encoding integer-dot decoding, ADC halfcell error, corner scaling and corner bound; pm_initialization attempts complete four integer-corner guard → current true E. Only independently replayed PASS declarations count. First pm_cell failed because of wrong cancellation lemma and final commutativity; failed logs with sorryAx are retained and excluded.

## Creative connections

1. Numerical-analysis error budgets become an assume/guarantee interface for control and compiler arithmetic. Preserve actual true-state recurrence, global clamp and actuator semantics; break it by averaging errors, changing decode, stale sampling or wrong word widths.
2. Ellipsoidal support identities become universal word-range bounds and allocation between fractional precision and accumulator width. Preserve correlation when proving state admission; a rectangular range enclosure alone is not safe admission.
3. ADC code as a set-valued measurement: exact integer corner checks plus convexity establish initialization. Propagate stale captures before initializing; a capture-time cell is not the current state. Later true-state induction does not need naive repeated startup initialization. Inventor's stronger contraction may additionally establish recurring cell admission under synchronized compliant updates.
4. Unexpected noise-shaping transfer: two opposite held command errors have zero sum yet nonzero final state because dynamics weight them differently. The result changes the required invariant, not the physical safety conclusion under bounded individual errors.

## Novelty / trusted boundaries

[VeriPhy2018](https://www.cs.cmu.edu/~smitsch/pdf/VeriPhy.pdf) already bridges real controllers, machine-word interval arithmetic and verified executables. [CompCert C reference](https://compcert.org/man/manual005.html) makes language/implementation semantics explicit. Checked2026-10-19. No novelty in the generic refinement idea is claimed. This campaign contributes source-specific contracts, concrete counterexamples and prototype arithmetic checks. Lean kernels/standard axioms, historical source-hashmatched dependency caches, native compiler, parser, ADC/DAC and physical model have different assurance scopes.

## Decision direction

GO for an exact, source-bound decoder/error/initialization consumer with20 declared mutations after breadth. Compiler/hardware assurance remains HOLD on named interfaces. Current-age and held-disturbance assumptions must remain visible. Quality and acceptance counts finalized in decision/card after independent replay.
