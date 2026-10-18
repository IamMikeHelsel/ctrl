# Source audit and a concrete invariant-choice result

18 October 2026. This note separates inspected source, a new hand derivation, finite checks, and existing Lean results. It does not select the author's intended operators.

## Source ledger

The [official homepage](https://geometricunity.org/) still identifies the April 2021 draft as its latest draft. The downloaded PDF is byte-identical to the prior local copy; see `source-refresh.json`.

Source-to-theorem map for the [2021 draft](https://geometricunity.nyc3.digitaloceanspaces.com/Geometric_Unity-Draft-April-1st-2021.pdf) (printed pages):

| Source | Local target | Boundary |
| --- | --- | --- |
| p.23, (3.26)–(3.27) | `splitMatrixEquiv_star`, `complexMatrixEquiv_bar`, `skew_iff_matrix` | Explicit conjugate-linear scalar convention. |
| p.23, (3.26)–(3.28) | `U_congruence`, `Uc_congruence`, half-index counts | Actual spinor signature (64,64), distinct from generator signature (7,7). |
| p.42, Definition 8.1 | Invariant-choice proposition below | Supplies two choices; does not choose one. |
| pp.41–43, (8.1), §8.2, (9.3) | Future operator theorem | Tensor normalization, bracket, curvature domain, and Bianchi assumptions need specification. |
| p.44, (9.4) | Future variation theorem | Action exists; independent fields and metric-dependent variation data need specification. |

The [2013 lecture transcript](https://theportal.group/a-portal-special-presentation-geometric-unity-a-first-look/), at 01:35:12 and 01:36:44, explicitly discusses Hodge-related invariants and alternatives between Lie and Jordan products. This supports treating the choices as intended freedom, not a contradiction.

The [2025 UCSD lecture](https://theportal.group/from-dark-to-geometric-energy-a-sector-of-geometric-unity/) and [2025 Jaimungal conversation](https://theportal.group/curt-jaimungal-with-eric-weinstein-geometric-unity-40-years-in-the-making/) were reopened. Targeted follow-up extraction timed out; the earlier saved transcripts remain the detailed evidence. No new normalized operator specification was located. This search does not cover all slides, video frames, private notes, or unindexed sources.

## Independent mathematical result: two explicit invariant choices

**Status: hand proof plus exact finite checks; not a new Lean-certified theorem in this directory.**

Let V be an oriented real quadratic space of signature (7,7). Fix an orthogonal basis e_0,...,e_13 with e_i²=+1 for i<7 and e_i²=-1 otherwise. Put A=Cl(V), A_C=C⊗_R A. Use Clifford conjugation † on A and its conjugate-linear extension on A_C. Thus v†=-v, (ab)†=b†a†, and i†=-i. Set U={a∈A_C : a†=-a}, a real vector space and real Lie algebra. This is the target corresponding to the already certified u(64,64) matrix form.

Let ω=e_0 e_1 ... e_13 be the **full volume element**. It is not the matrix K in the previous construction: K is a product of seven negative generators and implements the adjoint in an exterior basis.

The volume has the following properties:

1. ω²=(-1)^(14·13/2)∏e_i²=(-1)^91(-1)^7=1.
2. ω†=(-1)^(14·15/2)ω=-ω.
3. ωv=-vω for all v∈V. Consequently ω commutes with every even Clifford element.
4. If s is a Spin(7,7) element, sωs⁻¹=ω.

Write c_1(v)=v. Write c_2(u∧v)=(uv-vu)/2. The latter is the standard alternating linear map Λ²V→A. Define real-linear maps

F_1(v)=v,                  G_1(v)=ωv,
F_2(α)=c_2(α),              G_2(α)=iωc_2(α).

**Proposition.** For each r=1,2, F_r and G_r are linearly independent members of Hom_Spin(Λ^rV,U), over R. In particular, dim_R Hom_Spin(Λ^rV,U)≥2.

**Proof.** For v∈V,

(ωv)†=v†ω†=vω=-ωv.

Thus both F_1 and G_1 land in U. If B=c_2(α), then B†=-B and Bω=ωB. Hence (ωB)†=Bω=ωB, and

(iωB)†=-iωB.

Thus both F_2 and G_2 land in U. The standard Clifford inclusions intertwine the action of Spin on V and Λ²V with conjugation on A. Multiplication by ω preserves this equivariance, since ω commutes with every Spin element. Multiplication by the central scalar i also preserves it.

To prove independence, use the ordered Clifford monomial basis. F_1(e_0) has grade 1 while G_1(e_0) is a nonzero monomial of grade 13. F_2(e_0∧e_1)=e_0e_1 has grade 2 while G_2(e_0∧e_1)=iωe_0e_1 is a nonzero imaginary monomial of grade 12. Different grades have independent supports. A real relation aF_r+bG_r=0 evaluated at the named input forces a=b=0. ∎

The invariant bilinear form on V induces a nondegenerate Spin-invariant form on Λ^rV. It identifies Λ^rV with its real dual, giving

Hom_Spin(Λ^rV,U) ≅ [(Λ^rV)⊗_R U]^Spin.

Therefore the same lower bounds apply to the invariant tensor spaces. For an orthogonal exterior basis e_I, the tensors are explicitly Σ_I ε_I e_I⊗F_r(e_I) and Σ_I ε_I e_I⊗G_r(e_I), where ε_I=∏_{i∈I}e_i². No positive-definite inner product is assumed.

## Meaning and limitations

This is an explicit ambiguity result under a fixed adjoint, not an inconsistency result. Choosing a basis, a norm, or an orientation does not on its own pick a preferred line in a vector space of dimension at least two. An extra selection condition can do so. It is legitimate to impose that the output Clifford grade equal the input form degree, but that is an additional restriction and would exclude the displayed volume-twisted choices.

The target is a real Lie algebra. It is not closed under arbitrary multiplication by i. This explains why G_1 uses ω while G_2 needs iω. Treating U as a complex vector space would invalidate this argument's type signature.

The symmetry group is Spin. For a Pin action that reverses orientation, the volume changes sign, and the equivariance statement must change. The result does not claim invariance under all of U(64,64). In constructing the later operator, the auxiliary gauge conjugation acts on a selected invariant tensor; it does not replace the Spin group used to define that tensor.

The proposition provides a lower bound, not a classification of all invariants. It does not establish that the resulting Shiab operators are distinct on a chosen curvature domain. A bracket, projection, or Bianchi restriction could identify or kill some parameter directions. Testing that possibility needs the missing operator/domain definitions.

## Verification

`invariant_oracle.py` uses integer Gaussian coefficients and signed bitmask Clifford products. It checks the volume square and adjoint signs, 14 anticommutations, 91 even commutations, skewness and disjoint grade supports of all vector and bivector basis images, and 9,555 infinitesimal equivariance identities. The checked domain sizes are 14 and 91. See `invariant-oracle-result.json`.

These checks are independent of the prior matrix implementation. They support the hand derivation but are not a kernel proof of the invariant-space dimension theorem. Infinitesimal checks alone do not prove equivariance for all components of a group; the hand proof uses evenness of Spin elements directly.

## Paper framing

A defensible title is: “A certified split Clifford model and explicit operator-choice boundaries in Geometric Unity.” The concrete mathematical contribution is a reusable, checked construction and a precise separation of assumptions. Split Clifford algebra classification, Fock representations, Clifford conjugation, invariant volume twisting, and indefinite Hermitian signatures are standard mathematics. No new mathematical classification or physical prediction is claimed.

The useful new insight for this project is that operator underdetermination can be made explicit in the same algebra used by the proposal. It is not only an editorial request for more notation. There are at least two concrete invariant directions in each of the two low-degree tensor spaces under the chosen adjoint. A future formal operator study should expose these as parameters, prove conditions on those parameters, and only then compare with an author-selected instance.

A source-specific continuation needs a declaration that fixes: a real linear combination of invariant tensors for each Φ_r; all brackets and projections; the curvature subspace; star and orientation conventions; connection and torsion hypotheses; the variation's independent fields, support/boundary conditions, and pullback stage. The present proposition supplies candidate parameters without selecting their values.

## Later formal additions in this run

`VolumeTwist.lean` certifies the generic skew, conjugation, and independence arguments under explicit algebraic premises. `VolumeTwistActual.lean` discharges the non-scalar multiplier and invertible-input conditions for the actual full volume and first Clifford generator. It proves independence of the two generator-indexed maps and injectivity of their real affine family. These are algebraic theorems, not a complete formal invariant-tensor dimension theorem.

`QuadraticTwist.lean` studies an additional normalization condition. Define

F_(a,b)(v) = a v + b ωv.

For the actual vector inclusion, it proves

F_(a,b)(v)^2 = (a²-b²) Q(v) 1.

The Clifford square law is preserved for every v if and only if a²-b²=1. The forward implication is tested at the actual positive generator e_0. Thus even this additional condition leaves a hyperbola of choices. The rational point (5/3,4/3) is certified, differs from the original vector inclusion, and gives an actual Clifford-algebra endomorphism by the universal property.

This does not assert that the source requires Φ_1 to satisfy the Clifford relation. It answers a separate, explicit mathematical question: whether that plausible extra condition alone selects the untwisted inclusion. It does not. The coordinator's complementary conjugation analysis is important: different formulas can still be related by an inner algebra automorphism, so the parameter family does not establish inequivalent physics.

`GeneralBoost.lean` now proves the complete inner-equivalence result for this **particular normalized two-parameter family**. If a²-b²=1 and a≠-1, the element

T=(a+1)1+bω

has inverse ((a+1)1-bω)/(2(a+1)). Its conjugation sends v to av+bωv. If a=-1, normalization forces b=0, and conjugation by ω gives -v. Every displayed unit commutes with mathlib's `spinGroup Q`.

The quantifier is over this family, not all equivariant maps or all possible invariant tensors. Inner equivalence is also weaker than a specified physical gauge equivalence. For nonexceptional T, T†T=2(a+1)1. On the negative branch this factor is negative; no real scalar multiple makes that unit have adjoint norm +1. The exceptional volume has ω†ω=-1. Therefore the theorem must not be relabeled as equivalence by the intended U(64,64) gauge group without further analysis. The positive rational witness is compatible with the separate norm-three calculation in `RationalBoost.lean`.
