# M09 inventor — equivalence depends on the complete transported structure

AI-written by the cross-discipline inventor; inherited root model, exact identifier unavailable.
Original family H_t=K(I+tW), W²=-I, W†K=KW. The frozen FORM-CONGRUENCE.txt proves by
hand that S=aI+bW with a²-b²=1,2ab=t gives S†KS=H_t and commutes with represented Spin.
That broad coordinate statement is not a fixed-K unitary gauge transformation.

Sources read directly: frozen FORM-CONGRUENCE.txt and READ-ME.txt; primary GU2021 local
source text at /Users/mike/Documents/Codex/2026-10-18/do-more-work-with-a-team/exploration/sources/gu-2021.txt,
§3.6 (H=U(64,64)), §5.2 (bundle gauge sections) and §§5.3–5.4 (semidirect extension by
ad-valued one-forms and action on connections). The affine extension does not simply
replace its linear U(64,64) factor by arbitrary GL transformations. The actual fixed
Clifford/field/action comparison still needs its stated transformation laws.

## Three crossover mechanisms

1. **Observability and simultaneous-system realization.** In system identification, a
state-coordinate change must transport outputs and dynamics as well as the state metric.
Here use ψ_new=S^-1ψ_old, Γ_new=S^-1Γ_old S, H_new=S†K S. Both ψ†Hψ and
ψ†HΓψ are unchanged under this simultaneous transport. A convenient form congruence
alone proves no such statement with Γ frozen. Exact diagnostic below preserves values3
and5; freezing Γ instead gives40/17 and breaks its H-adjoint relation. Falsifier: an
implementation compares only forms, then reuses fixed operator matrices while claiming
all observables invariant. This transfers only algebraic observables, not a full GU action.

2. **Moving-frame kinematics and connection bookkeeping.** If the allowed passive frame
S varies, the derivative becomes D_new=∂+A with A=S^-1S' for a trivial old connection.
A constant old field need not have a constant new coordinate vector. Exact rational
parameterization below has nonzero ∂ψ_new but ∂ψ_new+Aψ_new=0. The changing metric
obeys H'=A†H+HA. The induced A fails A†K+KA=0, so it is not a connection coefficient
in the fixed-K unitary Lie algebra in that frame convention. A source ad-valued affine
shift therefore cannot be invoked without checking its type. Falsifier: erase A and
claim the varying-frame action unchanged, or label this A fixed-K anti-adjoint. This
variable-parameter test is a declared extension of the original constant-t question.
It establishes no nontrivial holonomy or new physical degree of freedom.

3. **Unexpected transfer: canonical phase-space volume as an extra acceptance invariant.**
An invertible coordinate map can preserve a desired quadratic expression while changing
a separately fixed area/symplectic structure. In the 2D diagnostic take the skew form W
as that additional structure. SᵀWS=(a²+b²)W=(17/8)W, so S is conformally symplectic,
not canonical. More generally a 2D symplectic map has determinant1, while
 det(H_t)=-(1+t²), det(K)=-1; it cannot produce unscaled H_t for t≠0. Normalizing S
by sqrt(a²+b²) changes the target to H_t/(a²+b²), which is a different normalization
contract. Falsifier: silently divide out this multiplier while a fixed form magnitude
or phase-space volume is part of the task. Symplectic structure is an explicitly added
diagnostic convention here, not an identified extra ingredient of GU. It helps design
an audit asking which other structures survive a proposed equivalence.

## Exact diagnostic and restricted-group boundary

`inventor_transport.py/json` uses K=diag(1,-1), W=[[0,1],[-1,0]], a=5/4,b=3/4,
t=15/8 and q=a²+b²=17/8. It verifies all foundational identities, inverse and congruence.
This is a 2x2 real diagnostic embedded in complex matrices, not the actual128-spinor
representation. Γ=K satisfies a positive K-adjoint convention; it is not claimed to be
the paper's Clifford-bar generator convention.

For ψ=(2,1), the transported ψ is(14/17,22/17). Its H-norm remains3 and the fully
transported observable remains5; freezing Γ gives40/17. The transported Γ still squares
toI and satisfies its declared H-adjoint relation. K itself is K-unitary and maps H_t
toH_-t in this toy, but anticommutes with W. Thus this sign flipper must not be described
as preserving W or every represented action pointwise.

Crucial conditional restriction: U†KU=K together with UW=WU implies U†H_tU=H_t.
Therefore a joint preservation contract is stricter than K-unitarity alone; it forbids
even sign reversal for nonzero t. No claim is made that every source Spin centralizer
must commute with W without inspecting that representation. `inventor_commutant.lean`
proves the abstract ring identities for preserving KW and K+KW, plus compatibility
with a commuting scalar multiplier. Its adjoint partner is an explicit algebraic input;
the theorem does not manufacture the source's admissibility assumptions.

For the varying-frame test use a(z)=(1+z²)/(1-z²), b(z)=2z/(1-z²) near z=1/3.
At that point A=(135/68)I+(18/17)W. The script independently checks derivative
compatibility and a constant-old-field cancellation exactly. It records the nonzero
fixed-K anti-adjoint defect and the conformal symplectic multiplier.

## Decision and next action

GO for a source-bound complete-structure transport checker: freeze whether K, represented
Spin action, Clifford generators and derivative/connection law are fixed or transported;
then test each required identity and reject a proposed equivalence upon the first failure.
Use the actual128-dimensional representation for the next bounded test, including the
sign flipper with its effect on the Spin embedding, and check any connection stays in
the declared adjoint bundle. HOLD on physical equivalence or a full action invariant
until those source field conventions are explicitly bound. The toy gives a discriminating
contract test, not a new GU observable or a classification of all invariant forms.

Evidence: exact rational matrix arithmetic and small abstract kernel identities; no physical
validation, source-action theorem, or novelty claim. Quality18/20 (faithfulness4,
reproducibility4,discrimination4,critique3,actionability3). Subjective algebra confidence98%.

Final kernel status: three declarations compiled with only propext. Frozen SHA256:
0429c0d74dc002e404adc67302e388988ca5299935e58ed29c58eecbdd6f39aa.
The matrix script also passes Ruff and an exact replay after formatting. Original files
and accepted source proofs were not changed.
