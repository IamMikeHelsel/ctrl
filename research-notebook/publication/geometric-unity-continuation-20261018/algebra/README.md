# Actual skew locus and full volume

`SkewLie.lean` uses the existing actual Clifford representation and actual form K.
It proves that Clifford conjugation's minus eigenspace corresponds bijectively to
matrices satisfying AᵀK + KA = 0. Both loci are closed under commutators. The matrix
locus is closed under addition and real scalar multiplication. The existing
explicit change of basis U carries this condition exactly to AᵀD + DA = 0,
where D has 64 positive and 64 negative diagonal entries.

This is the algebraic data for the real orthogonal Lie algebra identification.
The file does not package a Mathlib LieEquiv and does not prove dimension 8128.
It does not identify a physical GU operator.

`Chirality.lean` defines the full volume as the ordered product gamma 0 through
 gamma 13. It is distinct from K, which is the seven-negative-generator product.
The results below use this exact ordered product.

## Reproduction

Run `python3 algebra/verify.py` from this workspace. It uses the prior pinned
Lean 4.35.0 and Mathlib checkout. It rebuilds all 25 inherited source modules
and all four new modules plus the VolumeTwist and SpinEquivariance dependencies in a fresh directory, excluding the prior project build
cache. Dependency hashes, tool versions, and results are in verification.json.
`check.py` is a faster development check that reuses prior reviewed object files;
it is not the fresh-build evidence.

No frozen prior source is modified. No new axioms, sorry, admit, unsafe, or
native_decide are used. The axiom audit allows only propext, Classical.choice,
and Quot.sound.

## Full volume results

The full ordered volume ω satisfies ω² = 1 and star ω = −ω. It anticommutes
with each of the 14 actual generators, and hence with every actual vector.
It commutes with every product of two vectors. Thus both v and ωv belong to
the conjugation-skew locus, and their actual matrices are K-skew.

The volume is not a scalar. The theorem twisted_gamma_not_scalar_multiple
proves ω gamma0 is not any real scalar multiple of gamma0. This is a concrete
non-vacuity witness. The commutator action of each vector product commutes
with twisting by ω. These are algebraic equivariance identities. This module
does not define the Spin group or connect to the paper's chosen operator Phi1.
The full volume has not been identified entrywise with exterior parity.

Insight: the actual adjoint condition leaves at least two distinct vector
constructions, v and ωv. The condition alone cannot select a canonical GU
operator. Any uniqueness claim needs additional conditions or a specified
construction. This result does not settle which construction GU intends.

## Complex bivector choices

`ComplexChoices.lean` proves skewness of the actual normalized alternating
inclusion B(v,w)=(vw-wv)/2 and of iωB(v,w). Its bar operation is the existing
conjugate-linear Clifford adjoint. The factor i is therefore essential.

The element iω squares to −1, so it cannot be a real scalar. The bivector
B(e0,e1)=gamma0 gamma1 is a unit with explicit inverse gamma1 gamma0. The
independent-unit-twist lemma then proves real-linear independence of the two
actual functions on V×V. This proof uses no PBW support argument.

This module does not descend the alternating inclusion to a bundled exterior
power map, or define its Spin representation. Those remain separate interfaces.
The imported generic VolumeTwist source is pinned at SHA256
97e602b6664e5f0635ef344e01e8761077da2354f7021d6e8d776438f4f8041d.

## Nonunique Spin-invariant Hermitian forms

`HermitianFamily.lean` uses the actual complex matrix W representing iω. It
proves W²=−I. For every real t, set H_t=Kc(I+tW). The module proves:

- H_t is Hermitian.
- (1+t²)⁻¹(I−tW)Kc is both a left and right inverse.
- Every actual mathlib spinGroup matrix S satisfies S† H_t S=H_t.
- H_1 is not c Kc for any complex scalar c.

This gives a direct checked witness that Spin invariance is weaker than full
vector adjoint compatibility. The family is nondegenerate for every real t.
It does not use an assumed parity matrix. It does not classify all invariant
forms, prove the signature of every H_t, or choose a physical form.

The spinGroup bridge comes from spin/SpinEquivariance.lean. The group is the
exact mathlib definition; any identification with a different source convention
must preserve its unitary condition and even membership.
