# C03 domain: retained-state joint moment admission

AI-written, inherited root model; exact identifier unavailable. Original source: admission-04/analyst/report.txt, path frozen in CARD.md. No original source, plant, controller, or deadline was changed. The frozen research question asks for compact admission tests; diagnostic rejected deadlines below are alternative requests, not a replacement for the source's feasible task.

## Binding and strongest prior

The old arrival state at global1/4 is(q,v,a,j)=(5/192,5/16,5/2,10). With jerk limit10 and snap limit400, first zero acceleration without terminal-jerk constraint needs at least.30 seconds from that state. The old endpoint remains impossible, as source already established. The source also supplies a DIFFERENT feasible reference task: q=.6,v=a=j=0 by global1.5, corridor0≤q≤.6,0≤v≤1,|a|≤3,|j|≤10,|snap|≤400. Latency1/200 continues the old positive jerk, retaining every state. Execution at51/200 therefore begins at(44217/1600000,2601/8000,51/20,10). The exact scripts independently reproduce this state, not a reset approximation.

Primary check: [Berscheid–Kröger, RSS2021](https://arxiv.org/abs/2105.04830) states velocity/acceleration/jerk constraints and complete position/velocity/acceleration targets. That does not supply a snap constraint or terminal jerk condition. The existing source cites high-order planning by Ezair–Tassa–Shiller; fresh access to its author PDF returned403, so no fresh full-paper review is claimed. These elementary support-function arguments are not claimed novel or a complete time-optimal planner.

## Terminal jerk changes the area bound

For absolutely continuous j, j(0)=J,j(T)=0, |j|≤J, |j'|≤S almost everywhere,

    j(t) ≥ max(J−St,−J,−S(T−t)).

When T≥3J/S, its integral is at least−JT+5J²/(2S). The preliminary area bound T≥a0/J makes this regime applicable to the source state. Thus a(T)=j(T)=0 requires T≥a0/J+5J/(2S). With execution acceleration51/20 this is127/400=.3175. The original three snap phases(-400 for1/20,0 for97/400,+400 for1/40) attain it exactly, ending at(8782613/38400000,75089/96000,0,0). This establishes sharpness only for the first simultaneous a=j=0 event, not stopping.

Clock distinction: without latency, the old arrival state's simultaneous a=j=0 minimum is.3125; with the specified.005 latency, it is.3175 AFTER EXECUTION or.3225 after arrival. The old.30 result omitted terminal j=0 and used the original arrival state.

## New joint velocity–acceleration moment gate

Let I0=∫j and I1=∫t j. Terminal a=v=0 implies I0=−a0 and I1=v0. For p=t−α, endpoint snap envelopes give a compact support bound whenever2J/S≤α≤T−J/S:

    I1 ≤ −αa0 + J(α²−Tα+T²/2)
          −(3α+T)J²/(2S) + 3J³/(2S²).

Derivation: on negative p use j≥J−St until2J/S, then j≥−J. On positive p use j≤J untilT−J/S, then j≤S(T−t). Integrate these four polynomial pieces. The envelope maximizing this relaxation jumps from−J to+J atα: it is NOT an admissible finite-snap trajectory. A support upper bound remains sound and is not claimed attainable.

For source a0=51/20, v0=2601/8000, J10,S400, chooseα=(T+117/400)/2. The upper bound becomes

    B(T)=(5/2)T²−(127/80)T−13089/64000.

At T7/8, α467/800 and B=20511/64000. Required I1=2601/8000=20808/64000, giving exact rejection margin297/64000. Thus a complete stop cannot occur by global51/200+7/8=1.13. This is a necessary lower bound, not the earliest achievable stop. The source's actual constructive stop1.39718 and deadline1.5 are untouched; T249/200 gives B108423/64000>v0 and passes this necessary test.

Regime repair is explicit: the formula needsT≥137/400. A complete stop necessarily hasT>.5, because integrating j≥−10 gives0=v(T)≥2601/8000+(51/20)T−5T²; for0≤T≤.5 this is positive. Hence the optimizer's piece order is valid. Alternatively an earlier complete stop could be padded with exact rest to T7/8, maintaining all reference constraints; fixed-time rejection rules it out. Neither bridge applies to a mere a=0 event with positive velocity.

An admission implementation must return REJECT for a violated support inequality and UNKNOWN when necessary tests pass. ACCEPT needs a feasible trajectory certificate with all phase extrema, joins, latency history, corridor and derivative bounds checked. A passed scalar support test alone is not admission and never a closed-loop robot guarantee.

## Evidence and independent checks

`domain_dual.py/json` integrates all four support pieces with Fraction arithmetic, reconstructs the exact latency state and source three-phase blend, checks diagnostic T.8,T.875 and the unchanged source deadline. No solver is used. `domain_moments.lean` has eight conditional algebra/pointwise declarations. `domain_regime.lean` has two short-time/regime declarations. General fundamental-theorem/integration implications are hand proofs; there is no claimed complete ODE kernel theorem. An initial failed Lean draft is preserved in domain_moments_failed.log; corrected final proofs use only standard axioms.

`domain_independent.py/json` independently rederives critic's normalized marginal ranges and joint support bound without importing producer modules: individually feasible marginal target a1/2,v0,q17/192 atT1,J1,S4,j0=1,jT0 violates a−2v≤1/16. This is a declared separate diagnostic, demonstrating that marginal attainability is not joint attainability.

Also independently checked root's rest-to-rest snap fixture by hand: switches t1,t2,t3 satisfy t1+t3=T,t1t3=T²/8,t2=T/2. Zeroth through second snap moments vanish; third is−ST⁴/64, giving displacementST⁴/384. Peakjerk ST(√2−1)/2 is below10 atS400,T.1. No algebraic-number implementation is claimed for this independent hand check.

Next bounded test: assemble these dual rejections with a literal phase-certificate ACCEPT branch and retained-history hashes; independently reject mutations of terminal j, latency continuation, moment signs and threshold equality. The positive source reference certificate must remain separate from plant tracking and actuator acceptance. Quality18/20(90%); subjective confidence high in exact arithmetic and conditional gates, with the continuous execution bridge still hand-derived.

A load-bearing mutation is saved in domain_terminal_mutation.py/json: omit terminal j=0 and the final-ramp support correction disappears. At the same T7/8, optimizing the weaker gate givesα59/100 and upper8531/24000, exceeding requiredv0 by91/3000. The correct terminal-j gate rejects; the weaker necessary gate passes. This does not assert that the weakened task has a feasible trajectory. It shows why terminal jerk must be bound into the accepted question.
