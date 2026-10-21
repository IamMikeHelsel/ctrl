# M09 independent critique

The promising result is a **contract classification**, not a physical modulus. The source does not introduce our H_t family as an independent dynamical field alongside its chosen background K. The question therefore has several different mathematical answers depending on what is fixed.

Primary source binding: the local `gu-2021.txt` §§3.5–3.6 chooses H=U(64,64); §2.2 equation(2.7) and §6.2 require the inhomogeneous connection term; §8.1 and §9.3 dress canonical coefficient-valued Phi through epsilon. Accepted `HermitianFamily.lean` proves W²=−I, W†K=KW, Spin commutation and family invariance. The canonical Clifford adjoint wording in the source and its own warning about the Clifford decomposition do not uniquely settle every complex convention; the exact algebraic conclusions below bind to the accepted source-model bar.

## Contract outcomes

- Passive invertible coordinates: H_new=S†KS, Gamma_new=S⁻¹Gamma S, psi_new=S⁻¹psi and A_new=S⁻¹AS+S⁻¹dS. The displayed family has an all-real algebraic normalization once the coefficient existence and matrix identities are combined. A pointwise result does not prove global bundle/trivialization or full-action equivalence.
- Fixed-K gauge acting on an **additional declared form**: simultaneous congruence induces similarity of K⁻¹H. Its centered square is −t²I, so s²=t² is necessary. The actual negative-square gamma7 supplies a pointwise K-unitary sign flip, provided that source identity is accepted. A global gamma7 is not selected merely by choosing local Clifford coordinates. There is, however, a different conditional global construction: smooth global K,W on a paracompact base give null eigenbundles E±. A positive Hermitian h on E+ defines F:E+→E− by K(u,Fv)=h(u,v); swapping u+Fv↦v+Fu is K-unitary and reverses W. I independently checked the Hermitian conjugation and linearity. This is a hand bundle argument with source/global premises, not a freshly kernel-checked GU theorem.
- Fixed K plus W: admissible maps commuting with W preserve H_t exactly. Spin invariance is already proved in the accepted source. Commuting with Spin is not by itself the same as commuting with every Clifford generator, nor as being K-unitary.
- Same canonical Clifford generators and same negative adjoint: H_t Gamma+Gamma†H_t=2tKWGamma. Since all three factors are invertible, only t=0 works. This excludes nonzero t under that specific fixed-adjoint contract, not after passive transport.
- A decorated triple (K,H,W) has an additional signed trace invariant. This requires retaining K as a second structure and W as a specified decoration; it does not establish that GU treats them as independent fields.

Active and passive transport must not be conflated. Under the source active right gauge epsilon→epsilon h, bare canonical Phi can remain fixed while its dressed form transforms by h⁻¹(epsilon⁻¹Phi epsilon)h. In the passive basis test, the matrix representation of bare Phi/Gamma changes as well.

## Independent evidence

`critic_transport.py` consumes the inventor's serialized exact 2×2 receipt without importing producer code. It independently checks inverse, metric, generator, field, observable, moving-frame connection and metric-derivative bindings. Seven semantic mutations are rejected: frozen generator, wrong inverse, frozen field, omitted connection, frozen metric derivative, frozen metric, wrong parameter. Six signed rational hyperbola controls include t=0; they are finite checks, not the all-real proof. A noncentral K-unitary test preserves the relative square while leaving the displayed affine family, so family preservation cannot be assumed for arbitrary gauge elements.

`critic_adjoint.py` separately realifies a complex 2×2 example with Gamma=iK. It verifies the source-style negative K-adjoint, negative square, anticommution with W, K-unitarity, sign flip, nonzero fixed-adjoint defects and their repair under full passive transport. The moving-frame examples hold W fixed; varying W requires its derivative as well, or a stated covariant-parallelism premise relative to A0. This closes the convention mismatch in the inventor's useful Gamma=K toy without pretending either toy is the actual 128-dimensional representation. It also independently checks the active epsilon right-action with bare Phi fixed.

`critic_bridge.lean` proves fixed-K congruence→relative intertwining, conjugated multiplication, and the algebraic cancellation underlying a moving frame. All three compile with only propext. The derivative interpretation requires the separately stated differentiability/product/inverse rules; this lemma is not a global connection theorem. One inverse premise and one cancellation premise are redundant, harmless stronger hypotheses noted by the linter.

Independent generic compilation accepts domain8, inventor3 and critic3. The actual-source7 additionally pass independent original4.35 replay: gamma7 sign flip and fixed-adjoint t=0 obstruction are now kernel checked against the actual accepted representation. All28 imported research sources match the historical accepted cache; the dependency closure was not freshly rebuilt. Root10 final replay passes with matching source hashes, so **31 declarations** are independently accepted (domain15, inventor3, critic3, root10), all with permitted axioms. Earlier failed root/source attempts are retained and excluded. Failed or pending modules are not accepted based on printed theorem text alone.

`critic_pairs.py` independently reconstructs the root49 coordinate-pair diagnostics using4D realification instead of its2D routines. All49 preserve the decorated trace when the independent K is transported, and40 maps fail to preserve the old K. These finite diagnostics confirm the representation distinction; they add no physical/source-field claim.

## PM recommendation

GO for a typed, source-bound equivalence checker that forces an explicit choice of contract and verifies transported fields. NO-GO for calling the current broad congruence either a new physical degree of freedom or proof of unchanged full GU dynamics. HOLD global equivalence, source interpretation of H_t as a field, and complete action transport pending those exact inputs.

Quality rubric: provenance 4/4, assumptions 4/4, discrimination 4/4, independent evidence 4/4, scope completion 2/4 = **18/20**. Confidence is qualitative and subjective: high in the conditional algebra, unresolved in physical/source semantics.
