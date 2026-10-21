# M08 — GU curvature: convention-fixed bridge to draft9.3

**PM gate: GO for a source-bound operator certificate.** A complete finite-basis check now bridges the two representations under explicit conventions. It does not recover the author's uniquely intended operator. AI-written by root PM, domain, inventor and independent critic; inherited root model, exact identifier unavailable. Same-family role independence is not model-family diversity.

## Frozen question and provenance

Under explicit algebraic Riemann symmetries in signature(7,7), does the constructed commutator/Jordan Einstein contraction equal a convention-fixed version of draft equation9.3 after the Hodge identification?

Order21, math. Read the three frozen files in `/Users/mike/Dev/ctrl-research-notebook/research-notebook/publication/gu-source-exploration-20261018/`: `operator/OPERATOR-EXPLORATION.txt`, `operator/curvature_probe.py`, and `READ-ME.txt`. Their prior evidence comprised five exact examples and a hand derivation, not a curvature Lean theorem or a source correspondence proof. Originals remain unchanged.

Read and visually checked [Weinstein's2021 working draft](https://geometricunity.nyc3.digitaloceanspaces.com/Geometric_Unity-Draft-April-1st-2021.pdf), printedpp41–43 and65–66. The displayed nesting maps exterior2 to exterior13. Earlier discussion admits product choices, and the appendix defines both commutator and i-anticommutator. The displayed square brackets and invariant-form basis do not uniquely fix the choices used below; the draft reports unavailable earlier selection calculations. No author-error or novelty claim follows from this review.

## Three transfers and falsifiers

1. **Commuting-diagram verification.** Treat external Hodge/wedge operations and internal Clifford products as separate typed tensor legs. Verify each representation leg on a complete basis, then assemble by linearity. A Clifford volume twist is not an external Hodge map. Falsifiers: the mixed-sign sectional fixture and the all-positive fixture detect signs, factorials and missing Jordan i factors; consistent orientation reversal cannot repair the discovered relative minus.
2. **Representation decomposition and error-detecting redundancy.** Split the candidate into grade-one Einstein output and grade-five algebraic-Bianchi defect output. The latter is a redundant wedge map on a four-form. Any five retained rows determine the defect; four can miss one. This gives an implementation diagnostic with explicit erasure controls. It is not a physical sensor theorem or gauge-invariant positive norm. A nonzero defect can have zero indefinite metric norm.
3. **Unexpected differential-jet calibration.** Weyl annihilation alone cannot choose the scalar coefficient. Require divergence freedom on an explicitly admitted differential-curvature jet with nonzero scalar gradient. This selects the relative coefficient, while an algebraic-only field supplies a negative control. Crucially, differential gauge Bianchi and algebraic Riemann Bianchi are distinct obligations; an explicit commuting gauge connection separates them.

## Declared conventions and the bridge

`pm_convention_manifest.json` fixes metricdiag(+7,−7), orientationtheta0…theta13, sorted wedge coefficients, Clifford generatorsE_i²=s_i, canonical Phi1=sumtheta_i⊗E_i and Phi2=sum_i<jtheta_ij⊗E_iE_j. The tangent generator corresponds to s_i times the Clifford coframe generator under metric identification. Curvature uses the original sorted rho_ij; ordered four-index expansion carries1/4, with no unstated spin-curvature factor.

Use commutator in the first contraction and J(a,b)=i(ab+ba) in both scalar-composition contractions. For this **declared member of the displayed nesting**, the result is

`star(S_canonical(xi)) = -E_component(xi)`.

Replacing Phi1 by−Phi1 in **both** occurrences gives exact agreement with the earlier component candidate. Canonical exterior Hodge has star²0=−1, star²1=+1, star²2=−1. Reversing orientation consistently flips the exterior13 result and its identifying star together, leaving the identified operator unchanged; it does not remove the relative minus.

Root tested all8,281 exterior2×Clifford2 basis cases and16,384 exterior-blade Hodge-square identities. Critic independently verified1,274 vector/exterior contraction legs and8,281 bivector/exterior legs using tuple-based arithmetic. This representation translation does not require Riemann symmetries. Its Einstein interpretation does.

The mixed R0707=−1 fixture has scalar2 and Hodge-identified source output+2E_i on the12 transverse directions, zero on0,7, exactly the negative of the old candidate. Across eight C/J assignments at fixed canonical normalization, onlyC/J/J gives the target on a positive sectional fixture. All-commutator output is supported on the two sectional directions, whereas the Einstein target is supported on the12 transverse directions: no global rescaling repairs it. This selects within the declared eight-choice test, not within every invariant operator family or the author's intended convention.

## Complete algebraic-domain checks

Inventor and critic independently check all4,186 symmetric pair-coordinate inputs. On this domain the vector commutator gives2Ricci; the raw Phi2 anticommutator has scalar part−scalar and a four-form defect. For ordered distincta,b,c,d its coefficient is

`4*s_a*s_b*s_c*s_d*(R_abcd - R_acbd + R_adbc)`.

The extra component output is grade five, with rowi equal to e_i wedge that four-form. The negative R0123=R2301=1 has Ricci/scalar0 but ten nonzero grade-five rows of coefficient4. It is not a Weyl tensor: algebraic Bianchi fails.

Two thousand and two kernel combinations and all2,002 five-row subsets are checked. The defect map has rank1,001 and kernel3,185 by the displayed block decomposition. Four retained rows0,1,2,3 miss e0123; every five detect all defects. Minimum nonzero row support10 gives an exact block-code interpretation; no decoder or noisy physical guarantee is supplied. Coefficient Euclidean norm identities are frame diagnostics, not pseudo-Riemannian norm positivity.

Explicit right inverses strengthen the hand rank argument. For desired symmetric Einstein tensorT, set h=(T−tr_g(T)g/13)/24 and R=h wedge g. All105 coordinate targets reproduceT. For desired four-form coefficientq, use fully alternatingR_abcd=q/(12*s_a*s_b*s_c*s_d); five signature cases and a combined target pass. Thus the chosen pair-symmetric operator has rank1,106 and Weyl kernel dimension3,080 by hand assembly plus exact basis evidence. This is the classical algebraic decomposition in these conventions, not new physical content or a kernel rank theorem.

## Differential and gauge controls

The explicit local connection

`A=(1/2)e23(x0 dx1−x1 dx0)+(1/2)e01(x2 dx3−x3 dx2)`

has commuting coefficients, A wedge A=0, constant F=e23 dx01+e01 dx23, and d_AF=0 everywhere. Its algebraic cyclic curvature defect is nonzero. Independent polynomial arithmetic verifies it. No Levi-Civita/soldering compatibility is claimed; that missing condition is exactly why gauge Bianchi cannot license the earlier Riemann simplification.

For E_beta=2Ric−beta*scalar*g, all beta annihilate Weyl. A symmetric third-order tensor H000=1 defines the formal jet D_mR_ijkl=H_ikm*g_jl+H_jlm*g_ik−H_ilm*g_jk−H_jkm*g_il. All537,824 algebraic and differential cyclic component checks pass; divRic=(13,0,…), dscalar=(26,0,…). Its E_beta divergence is26(1−beta), so divergence freedom selects beta1. Domain independently checks13,720 contracted components across five signed symmetricH seeds; critic independently replays the sparse jet. This is a formal jet and conditional selection test, not a constructed global metric or the full GU gauge identity. An affine sectional fieldK=x0 has13/182 instead and violates differential contracted Bianchi; substituting it would falsely select beta1/7.

Raw Clifford-grade diagnostics also require a bound frame. A rational complex Clifford conjugation mixes e0 with i*e123 and mixes a five-blade with a two-blade. The algebraic calculation is independently checked; admissibility in the author's precise epsilon group is not inferred. A covariance test must conjugate Phi and input together. Our experiments fix epsilon=identity.

## Acceptance, decision and next action

Fourteen isolated Lean declarations independently compile with permitted axioms, covering concrete basis signs and conditional normalization arithmetic. `pm_lean_acceptance.json` and `critic_acceptance.json` record hashes/logs. Complete finite-basis evidence and linearity/decomposition assembly remain exact Python plus hand reasoning; no full typed source-operator Lean theorem, Python refinement, global metric realization, physical validation or author-selected equivalence is accepted.

GO after all60 initial reviews: one30-minute block to build the typed, manifest-bound Hodge/Clifford operator certificate and promote the general basis/linearity bridge. Freeze20 heldout/mutation cases including product tags, sign/normalization, metric raising, sorted/ordered factorials, tensor-leg confusion, orientation, gauge transport, Bianchi-domain swaps and defective input. Require both a canonical negative-sign and matched-Phi1 positive example, plus independent rejection of false Einstein simplification. Keep source-intended selection HOLD pending explicit normalization/product evidence; do not replace missing evidence with numerical agreement.

Quality: faithfulness4, reproducibility4, discrimination4, independent critique4, actionability3 = **19/20 (95%)**. Subjective confidence is high in the explicit finite checks; source-intended and physical significance remain unresolved. No calibrated novelty or success probability assigned. Actual substantive time is recorded in state.json, excluding setup and gaps.
