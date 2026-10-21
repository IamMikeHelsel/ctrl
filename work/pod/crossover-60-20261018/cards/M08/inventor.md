# M08 — inventor review

AI-written cross-discipline research. Inherited model identifier is unavailable. Own scope is `inventor*`; original sources were read only. This is the initial review, not an extended investigation. The PM owns timing and the decision.

The useful new boundary is concrete: the differential gauge Bianchi identity does **not** justify imposing algebraic Riemann Bianchi symmetry. An explicit commuting gauge connection satisfies the former everywhere while producing the extra Clifford grade-five terms that the old Ricci-only probe omitted.

## Source and fixed interpretation

Read `operator/OPERATOR-EXPLORATION.txt`, `operator/curvature_probe.py`, the frozen card, and the primary draft's printed pages41–43 and appendix definitions12.25–12.27. Visually inspected the page43 equation. Primary source: [GU draft, April2021](https://geometricunity.nyc3.digitaloceanspaces.com/Geometric_Unity-Draft-April-1st-2021.pdf). Local original is `/Users/mike/Documents/Codex/2026-10-18/do-more-work-with-a-team/exploration/sources/gu-2021.pdf`.

The source specifies a degree-two to degree-thirteen base-form map in dimension14 and leaves an operator family/choice issue. A component calculation is conditional on a manifest fixing orientation, sorted exterior basis, raised Clifford indices, the normalizations of Phi1/Phi2, epsilon=identity, and each commutator/Jordan choice. The pod's canonical C/J/J interpretation and its Hodge sign are a declared reconstruction, not recovered author instructions. The PM/domain independently examine that bridge; my complementary computation concerns its domain of validity.

Base differential-form degree and internal Clifford grade are different gradings throughout. The following E_i has base degree one after the declared Hodge identification, but may have internal Clifford grades one and five.

## Transfer1: compiler translation validation / commuting diagram

Map the typed source expression, sparse exterior implementation and component contraction through an explicit convention manifest. Preserve the *whole* linear map, not just five values or a trace. Equality on a spanning basis is informative only when the domain relations and both representation maps are independently checked.

Small falsifiers: reverse the orientation; remove one Jordan factor i; insert an inappropriate factorial into a sorted basis; or replace the fourteen-dimensional Hodge square with its positive-definite sign. Each mutation must have a named witness. A negative result on a Bianchi-violating input cannot refute equality restricted to algebraic Riemann tensors. Conversely, accepting only Riemann fixtures cannot authorize the full gauge-curvature domain.

This transfer's strongest next test is a source-bound certificate checking a basis for the *declared* domain and the two sides independently. It breaks when both implementations share the same faulty conversion or when an unspecified source bracket is silently selected.

## Transfer2: constraint residuals / algebraic Bianchi defect

Use the forbidden grade as a residual, rather than erase it. With s_i=+1 for i<7 and −1 otherwise, let

- rho_ij = sum(k<l) s_k s_l R_ijkl e_k e_l;
- Qraw = sum(i<j) s_i s_j {e_i e_j,rho_ij}, with raw anticommutator;
- C_i = sum(j) s_j [e_j,rho_ji];
- E_i = C_i + (1/2){e_i,Qraw}, accounting for the two Jordan i factors.

For pair-antisymmetric, pair-symmetric R, without assuming cyclic Bianchi,

`Qraw = −scal + Q4`,

`(Q4)_abcd = 4 s_a s_b s_c s_d (R_abcd − R_acbd + R_adbc)` for a<b<c<d,

`C_i = 2 sum_l s_l Ric_il e_l`,

and the grade-five component is exactly `E5_i = e_i wedge Q4`.

`inventor_defect.py` independently reduces Clifford words by insertion and cancellation. Exact Fraction tests cover all4,186 coordinate basis vectors of Sym²(Lambda²), and2,002 explicit kernel combinations on the1,001 quadruples. They verify the scalar/grade-four decomposition, C/Ricci identity, and the extra-grade formula. The disjoint quadruple blocks give defect rank1,001 and cyclic-Bianchi kernel dimension3,185. This is finite exact executable evidence plus linearity reasoning, not a Lean proof.

Negative fixture R0123=R2301=1 (with pair antisymmetry) has zero Ricci and `Qraw=4e0123`. E_i has coefficient4 on e0123i for each i=4,...,13: ten nonzero internal grade-five rows. It is not a Weyl tensor because it fails cyclic Bianchi. The original probe correctly recorded its defect but skipped E evaluation outside its `expect_bianchi` branch; my test evaluates that previously omitted output.

A hand decomposition further predicts full map rank1,106 and kernel dimension3,080 on pair-symmetric inputs. Reason: Ricci is onto Sym² via Kulkarni–Nomizu h∧g, with Ricci=12h+(trace h)g in dimension14; the Einstein transform is invertible there since its trace multiplier is−6. Fully alternating four-tensors independently realize every Q4 and have zero Ricci. E5 is injective in Q4. Thus the two output grades separate105 Ricci coordinates and1,001 defect coordinates. This is a derivation, not an independently kernel-checked rank certificate or a novelty claim.

**Differential Bianchi falsifier.** `inventor_connection.py` verifies the local gauge connection

`A = (1/2)e23(x0 dx1 − x1 dx0) + (1/2)e01(x2 dx3 − x3 dx2)`.

The bivectors e01 and e23 commute. Therefore A wedge A=0 and

`F = e23 dx0 wedge dx1 + e01 dx2 wedge dx3`.

F is constant and commutes with A, so `d_A F=0` identically. Its algebraic cyclic0123 expression is1. This lives in four positive directions embedded in signature(7,7), on a local trivial gauge bundle. It is not asserted to be Levi-Civita curvature compatible with a soldering form. It refutes importing algebraic Bianchi from differential gauge Bianchi alone; it does not refute the source's Weyl-annihilation statement on a Riemannian subspace.

## Transfer3 (unexpected): an exact block code for implementation diagnostics

The redundant map `Q4 -> (e_i wedge Q4)_i` behaves as a linear block code. A nonzero four-form has at most four zero rows: for a row to vanish, every nonzero coordinate monomial must contain that row's index. Each monomial contains only four indices. A coordinate four-blade has exactly ten nonzero rows, so minimum block distance is10.

Consequences in exact arithmetic: any five retained rows determine Q4; up to four arbitrary whole-row corruptions are uniquely correctable in principle; five may create ambiguity. No decoder is supplied. These are implementation-audit statements, not a physical sensor-fault model.

`inventor_redundancy.py` checks all2,002 choices of five retained rows. With k retained coordinate rows, the kernel has dimension C(14−k,4−k) for k<=4 and zero for k>=5. Falsifier at the sharp boundary: retain only rows0,1,2,3; Q4=e0123 is invisible. Splitting its ten nonzero rows into two groups of five makes a received word equally compatible with zero and that message under five row errors.

An additional exact check is `sum_i ||E5_i||coord² = 10 ||Q4||coord²`. The positive coordinate norm here is **not** invariant under noncompact Spin(7,7). Grade extraction presupposes the fixed Clifford identification; arbitrary full gauge conjugations need not preserve these grade labels. Duplicating a row is not a new independent check.

## Evidence and next action

Three own scripts and JSON outputs are the finite exact evidence. No source file, approved challenge, or public CLI was changed. No physical validation, solver certificate, full gauge theorem, or novelty assessment is claimed. The source-selected normalizations and generic gauge interpretation remain separate questions.

Recommendation to PM: GO for a bounded source-bound basis/certificate adapter, with the commuting-connection negative permanently included. NO-GO for inferring the Ricci-only formula from differential gauge Bianchi alone. Preserve both grade-one and grade-five outputs until algebraic cyclic symmetry is actually established.

Proposed next acceptance tests: reject a manifest with a missing Jordan factor; reject a consumer that silently drops nonzero grade five; distinguish a four-row incomplete check from a five-row check; and bind the tested domain relations to the theorem statement. These are useful falsifiers, not redundant theorem packaging.

Quality rubric: source binding4/5, explicit transfer mechanisms4/4, discriminating tests5/5, independent-check readiness3/3, scope discipline3/3 =19/20. Subjective confidence in the exact algebraic findings95%; confidence in reproducing the author's intended operator is not assigned from these tests.

## Supplement: explicit right inverse for the rank claim

For a desired symmetric covariant Einstein-output tensor T, use

`h = (T − tr_g(T) g/13)/24`, and `R = h wedge_KN g`.

Here the Kulkarni–Nomizu convention is exactly

`R_ijkl = h_ik g_jl + h_jl g_ik − h_il g_jk − h_jk g_il`.

It gives `Ric=12h+tr_g(h)g`, `scal=26tr_g(h)`, and hence `E_tensor=24(h−tr_g(h)g)`. The chosen h has trace `−tr_g(T)/312`, so `E_tensor=T`. Internal degree-one row coefficients are `s_l T_il`; omitting that final raising sign would change the test.

Independently, for desired sorted four-form coefficients q_abcd, set the fully alternating tensor's sorted component to `q_abcd/(12 s_a s_b s_c s_d)`. Its Ricci contraction vanishes. Its cyclic defect is three times its sorted component, so its Q4 coefficient is q_abcd. Adding these two tensors yields arbitrary independent symmetric grade-one and allowed grade-five outputs. This supplies an explicit general right inverse, strengthening the hand rank argument; it does not establish global metric realization.

`inventor_right_inverse.py` evaluates the actual Clifford contractions for all105 symmetric coordinate targets, five pure four-form targets covering zero through four negative-sign indices, and one combined target. It imports and reruns the earlier finite basis audit. Its output is stored separately in `inventor_right_inverse.json`; this supplement does not convert the hand general assembly into a Lean theorem.
