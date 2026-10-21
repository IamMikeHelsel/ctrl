# M08 domain: a convention-fixed Hodge bridge

AI-generated research; inherited root model, exact runtime identifier unavailable. Original source and proof bundles unchanged. The prior five examples establish a bounded candidate only, with no prior exterior-Hodge identification or kernel proof of the complete curvature identities.

## Primary-source binding

The [working draft](https://geometricunity.nyc3.digitaloceanspaces.com/Geometric_Unity-Draft-April-1st-2021.pdf), pp41–43 and65–66, was read in text and equation9.3 was visually inspected using the PDF skill. Equation8.1 describes a family with Hodge operations and commutator/imaginary-anticommutator choices. Definition8.1/8.7 supplies invariant tensor spaces; it does not fix our basis signs or all normalizations. Equation9.2 has output degree13. In9.3 the first product has degree13, while the second term has an outer Hodge applied to degree1. Appendix12.25 defines the displayed contraction by star-wedge-star;12.26 defines the commutator;12.27 defines the imaginary anticommutator. The text reports missing original operator-selection notes. These passages support testing an explicit family member, not identifying a unique author-selected implementation.

Literal square brackets in9.3 would naturally follow12.26. On the old pair-symmetric bivector curvature sector, an all-commutator reading has zero inner double contraction and hence no scalar correction. The tested commutator/Jordan/Jordan assignment is therefore an explicitly declared version within the earlier family, not a demonstrated unique literal reading of the printed9.3.

## Declared conventions

At one point take epsilon=identity, an orthonormal tangent frame E_i, i=0,...,13, signature s_i=+1 for i<7 and−1 otherwise, and dual coframe theta_i. Exterior orientation is theta_0 wedge...wedge theta_13. Clifford products satisfy E_i E_j+E_j E_i=2s_i delta_ij. Via the metric identification with source Cl(T*), E_i corresponds to s_i times gamma(theta_i). This distinction prevents accidentally inserting a second set of metric signs into the solder tensors.

Choose Phi1=sum_i theta_i tensor E_i and Phi2=sum_i<j theta_ij tensor E_i E_j. Choose rho_ij=sum_k<l s_k s_l R_ijkl E_k E_l and xi=sum_i<j theta_ij tensor rho_ij. The exterior sum equals one-half the ordered i,j sum; rho likewise equals one-half the ordered k,l sum. Thus an all-ordered four-index expression has coefficient1/4. Changing a spin-curvature normalization rescales xi; it must not be silently identified with a different author's convention.

For an ordered subset I, define

*theta_I = sign(I,I-complement) product_i-in-I(s_i) theta_(I-complement).

Then *² on degreep is (-1)^[p(14-p)+7]: negative on0,2,14 and positive on1,13. The final identifying star takes the degree13 source expression to degree1. Exterior degree and internal Clifford grade are independent throughout.

## Mixed-sign basis result

Take the algebraic sectional tensor R_0707=−1 and its pair-symmetry completion. It gives rho_07=E0E7. The old component contractions have Ric_00=1, Ric_77=−1, scalar2; C0=2E0,C7=2E7, all other C_i=0; D_i=4E_i. Hence E=C−D/2 vanishes in directions0,7 and equals−2E_i in the twelve transverse directions.

The exterior calculation gives

*(theta0 wedge *theta07)=−theta7,
*(theta7 wedge *theta07)=−theta0.

The source inner scalar contraction before its Jordan factor i is+2; the old component scalar contraction before i is−2. Including both factors of i, applying the final star to the declared source comm/J/J expression yields−E: zero on0,7 and+2E_i on the twelve transverse directions. `domain_mixed_case.py/json` computes this directly with sparse exterior and Clifford products, exact Fraction coefficients and explicit i²=−1. It does not import the original probe. Scoped Ruff passes.

Thus the prior proposed identification missed a global sign under these conventions. Reversing Phi1 in BOTH occurrences repairs it. Reversing orientation consistently does not: the source degree13 expression changes sign, but the final identifying star also changes sign. Their composition is unchanged.

More generally Phi1→p Phi1, Phi2→q Phi2 and xi→t xi gives identified output−p*t*(C−qD/2). A global factor cannot repair an arbitrary q: the relative scalar coefficient must be fixed separately. With t=1, p=−1, q=1 the identified expression equals the old component E.

## Internal volume is not a substitute for exterior star

For an ordered Clifford blade E_I of degreep and volume omega=E0...E13, direct multiplication gives

E_I omega = (-1)^[p(p−1)/2] *E_I,

under the declared basis identification. Left multiplication adds the sign(-1)^[p(14−p)]. This follows by expressing omega as sign(I,Ic) E_I E_Ic and using E_I²=(-1)^[p(p−1)/2] product_i-in-I(s_i). The star in this identity is the metric basis map on that Clifford vector space, not an operation on the independent exterior factor of a bundle-valued form. In particular omega²=+1 while exterior *² on degree0 is−1. The draft's volume analogy does not license replacing every Hodge star with unqualified Clifford multiplication.

## Relative normalization and differential Bianchi

For the family E_beta=2Ric−beta*scal*g, every beta annihilates Weyl curvature, so Weyl annihilation cannot select beta. In dimension14 its trace is(2−14beta)*scal. If a genuine Levi-Civita contracted differential Bianchi identity supplies divRic=(1/2)dscal and the metric is parallel, then divE_beta=(1−beta)dscal. Requiring this to vanish for every allowed nonconstant scalar gradient selects beta=1. Constant scalar curvature tests cannot make that selection.

The conditional scalar-component kernel lemmas in `domain_beta.lean` keep the geometric premise explicit. The concrete compatible derivative test dr=1/2, ds=1 selects beta=1; it is a formal local derivative test, not a constructed GU solution. A useful negative control is the algebraic curvature field with sectional curvature K(x)=x0. Pointwise it obeys the algebraic curvature identities, but dr=13 and ds=182, violating2dr=ds. In that field beta=1/7, not1, cancels the displayed divergence component. This field is not asserted to be the Levi-Civita curvature of a metric: it demonstrates exactly why pointwise algebraic Bianchi cannot replace differential integrability. Neither identity is interchangeable with the general gauge identity d_A F_A=0 without additional structure.

## Evidence and decision scope

`domain_hodge.lean` has six locally accepted declarations: exact Fin14 mixed-basis wedge/Hodge signs, relevant *² parity values and coefficient assembly. Only propext, Classical.choice, Quot.sound appear. These are a finite convention check, not a kernel proof of all curvature identities or of the source's invariant-tensor selection. `domain_beta.lean` is a separate conditional coefficient proof; its compile/independent status is recorded below. Root's full linear-basis experiment is separate evidence and is not inferred from this one mixed-sign example.

Suggested decision: GO for the explicitly declared representation bridge and differential-normalization test; HOLD any claim that the printed source uniquely chooses comm/J/J, these tensors or the full gauge-curvature domain. Precise next action: freeze the full convention ledger, independently certify the all-basis exterior/component equality, then prove the Riemann-sector identities and identify which source sector supplies differential Bianchi. Quality grade4/5 for the bounded bridge. Subjective confidence high in the exact tested signs; no physical or novelty claim.

## Explicit differentially admitted jet

Root supplies a stronger positive formal jet than the scalar placeholder: fully symmetric H_ikm with H000=1, and

D_mR_ijkl = H_ikm*g_jl + H_jlm*g_ik − H_ilm*g_jk − H_jkm*g_il.

Independent contraction gives, for T_m=sum_j s_j H_jjm,

D_mRic_il =12 H_ilm+T_m*g_il,
divRic_l=13T_l,
dscal_m=26T_m.

Full symmetry of H identifies the contracted H term with T, and the differential cyclic identity cancels term by term. With H000=1, T=(1,0,...,0); thus this nonzero differentially admitted derivative fixture gives divE_beta=26(1−beta) in direction0. Unlike the affine sectional K=x0 negative control, it meets the contracted differential premise. This is a formal first curvature-derivative jet, not a claimed global metric or GU solution.

`domain_jet_check.py/json` independently verifies13,720 Ricci-derivative entries across five symmetric cubic H seeds, including mixed-sign traces, and matches the root fixture's divergence and scalar-gradient fields without producer imports. `domain_jet.lean` adds two conditional exact coefficient lemmas for the13/26 result. `domain_beta.lean` six and `domain_jet.lean` two declarations compile exit0 with permitted axioms. Together with the six Hodge declarations, all14 domain statements are locally accepted. Independent critic replay is a separate gate. Scripts pass scoped Ruff checks; original files remain unchanged.
