# Controls / Estimation / Vision backlog assessment (issues #4–#9)

Author: claude · 2026-10-17 · Lean `v4.36.0-rc1`, Mathlib as pinned in `lake-manifest.json`.

Method: for each issue I read the issue text and comments, checked open PRs and remote branches
for claims, grepped Mathlib (`.lake/packages/mathlib/Mathlib`) for the needed API, and grepped
`LeanForControl` (`~/Dev/LeanForControl`) for prior art.

**Claim status (as of 10:45 PT):** none of #4–#9 had comments, assignees, or branches. The only
other branch was `claude/bounty-lane` (PR #1, docs only). `main` already contains
`Controls/PolePlacement.lean`, a 2×2 companion-form special case of #8 with no issue link.
I have now claimed **#6**; see draft PR #10.

## Summary

| # | Topic | Verdict | Est. lines | Prior art |
|---|-------|---------|-----------:|-----------|
| 4 | Observability ⇔ dual controllability | Feasible, medium | 120–180 | LeanForControl has the matrix-rank version (via Cayley–Hamilton) |
| 5 | Jury test, degree 2 | Very tractable, small | 80–120 | none found |
| 6 | Scalar Riccati convergence | **Done: PR #10** | 115 | none found |
| 7 | Converse discrete Lyapunov | Feasible, medium; **already in LeanForControl** | 150–250 | `IsSchur.exists_posDef_unique_solution_discrete_lyapunov` |
| 8 | Single-input pole placement (general n) | Hard, large | 400–700 | 2×2 case on `main`; nothing general anywhere |
| 9 | Eight-point algorithm: E unique up to scale | Tractable, small–medium | 60–100 | none found |

Recommended order after #6: **#5**, then **#9**, then **#4**. Deprioritise **#7**, which
duplicates LeanForControl. Treat **#8** as a multi-PR project.

---

## #4 Observability as the dual of controllability

**Statement.** For `A : V →ₗ V`, `C : V →ₗ Y`, define the unobservable subspace
`unobs A C k = ⨅ i < k, ker (C ∘ₗ A^i)`. Then (a) it stabilises at `k = dim V`, and
(b) `unobs A C k = (reach A.dualMap C.dualMap k).dualCoannihilator`. So `(A, C)` is observable
iff `(Aᵀ, Cᵀ)` is controllable.

**Mathlib API** (all present):
- `LinearMap.ker_dualMap_eq_dualCoannihilator_range` (Dual/Defs.lean:493)
- `LinearMap.range_dualMap_eq_dualAnnihilator_ker` (Dual/Lemmas.lean:825, field case)
- `Submodule.dualCoannihilator_iSup_eq`, `dualAnnihilator_iSup_eq` (Dual/Defs.lean:425–429)
- `Subspace.dualAnnihilator_dualCoannihilator_eq` (Dual/Lemmas.lean:433)
- `Submodule.dualCoannihilator_top`, `dualAnnihilator_bot/top`
- Matrix route: `Matrix.rank_transpose` (Matrix/Rank.lean:568)

**Proof sketch.** Use `reach_eq_iSup` on the dual system:
`reach Aᵀ Cᵀ k = ⨆ i<k, range ((Aᵀ)^i ∘ Cᵀ) = ⨆ i<k, range ((C ∘ A^i)ᵀ)`. Push
`dualCoannihilator` through `⨆` to get `⨅ i<k, ker (C ∘ A^i)`. Stabilisation then
follows from `reach_eq_reach_finrank` on the dual side, using `finrank (Dual K V) = finrank K V`.
You can also prove stabilisation directly with the dimension-counting argument from
`Reachability`, applied to the decreasing chain.

**Risks.** `dualMap` of a power: `(A^i).dualMap = A.dualMap^i` needs a small induction
(`LinearMap.dualMap_comp_dualMap`). The coannihilator lemmas need a `Field` and finite
dimensions. Novelty versus LeanForControl is the coordinate-free, Cayley–Hamilton-free
statement, which is worth saying explicitly in the PR.

**Estimate.** 120–180 lines. Medium.

## #5 Jury stability test for degree 2

**Statement.** Every complex root of `z² + a z + b` (with `a, b : ℝ`) has `‖z‖ < 1` iff `|b| < 1`
and `|a| < 1 + b`.

**Mathlib API.** Same toolkit as `Hurwitz2`: `Complex.ext_iff`, `Complex.abs`/`norm` via
`Complex.sq_norm`/`normSq`, `Real.sqrt`, `nlinarith`. Nothing missing.

**Proof sketch.** Split on the discriminant `d = a² − 4b`.
- `d < 0`: the roots are conjugate with `‖z‖² = b`, so the condition is `b < 1`. Since `b > a²/4 ≥ 0`,
  `|a| < 2√b ≤ 1 + b` holds automatically (AM–GM).
- `d ≥ 0`: the roots are `r± = (−a ± √d)/2`. Both lie in `(−1, 1)` iff `p(1) > 0`, `p(−1) > 0` and
  `|a| < 2`. Here `p(±1) = 1 ± a + b`, and `|a| < 2` follows from the other two conditions together with `b < 1`.
- For (⇒), exhibit an explicit root with `‖z‖ ≥ 1`, mirroring `exists_root_re_nonneg`.

**Risks.** Mostly `nlinarith` tuning in the real-root case. The statement must quantify over
complex roots, using the norm and not `.re`. Optional corollary: discretised PD loop gains.

**Estimate.** 80–120 lines. Small. **Second most tractable.**

## #6 Scalar Riccati iteration converges (implemented)

**Statement.** For `R, Q > 0` and any `P₀ ≥ 0` (generalising the issue's `P₀ > 0`, at no cost):
`(riccati R Q)^[k] P₀ → steadyState R Q`, with rate
`|P_{k+1} − S| ≤ ((R/(Q+R))²)ᵏ |P₁ − S|`. The Kalman gain also converges to `S/(S+R)`.

**Mathlib API.** `tendsto_pow_atTop_nhds_zero_of_lt_one`, `squeeze_zero`,
`tendsto_add_atTop_iff_nat`, `tendsto_iff_norm_sub_tendsto_zero`, `Function.iterate_succ_apply'`,
`Filter.Tendsto.div`.

**Proof.** `riccati P ≥ Q` whenever `P ≥ 0`, so every iterate after the first is `≥ Q`. With
`S > Q`, `min P S ≥ Q`, so the `riccati_lipschitz` constant is at most `(R/(Q+R))² < 1`. Then
induct on `k` and squeeze.

**Result.** `ControlsLean/Estimation/RiccatiConvergence.lean` is about 115 lines.
`scripts/check.sh` passes on the branch (32 headline theorems audited, standard axioms only).
Draft PR: https://github.com/IamMikeHelsel/ctrl/pull/10

## #7 Converse discrete Lyapunov theorem

**Statement.** If `A^k → 0`, then `P = Σ (Aᵀ)^k Q A^k` converges, `P ≻ 0` for `Q ≻ 0`, and
`P − AᵀPA = Q`.

**Mathlib API.**
- A matrix norm instance is needed locally: `Matrix.linftyOpNormedRing` / `Matrix.frobeniusNormedRing`
  (Analysis/Matrix/Normed.lean).
- `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`, `summable_of_isBigO_nat`, `Summable.tsum_mul_left`,
  `Summable.tsum_mul_right`, `Summable.tsum_eq_zero_add` (telescoping), and continuity of
  `transpose` and `mul` for pushing through `tsum`.
- Alternative route: Gelfand's formula `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`.

**Proof sketch.** `A^k → 0` gives some `N` with `‖A^N‖ ≤ 1/2`, so `‖A^k‖ ≤ C·(1/2)^{k/N}` and the
sum is summable. Then `AᵀPA = Σ_{k≥1}`, so `P − AᵀPA = Q`. Positive definiteness holds because
`xᵀPx ≥ xᵀQx > 0`, since each term is PSD (the tsum of nonnegative reals).

**Risks.** Matrix norm instances are not global, which makes for instance friction. Going from
tsum to quadratic forms needs `Matrix.tsum_apply`-style lemmas. **Prior art:** LeanForControl
already proves `IsSchur.exists_posDef_unique_solution_discrete_lyapunov` and
`isSchur_iff_forall_posDef_exists_discrete_solution`. This issue adds little except pairing with
`ctrl`'s symmetry-free forward direction.

**Estimate.** 150–250 lines. Medium. Low novelty.

## #8 Pole placement for single-input controllable systems

**Statement.** If `(A, b)` is controllable (`n × n`, single input), then for every monic `p` of degree `n`
there is a `k` with `charpoly (A + b kᵀ) = p`.

**Mathlib API.** `Matrix.charpoly`, `charmatrix`, `Matrix.charpoly_fin_two`, `det_fin_two`,
`Matrix.charpoly_reindex`/similarity invariance (`charpoly` of `P⁻¹ A P`), Cayley–Hamilton
`aeval_self_charpoly`. **Missing:** the companion matrix and its characteristic polynomial
(`grep companion` finds nothing relevant in Mathlib).

**Proof sketch.** (1) Build the Krylov basis `b, Ab, …, A^{n−1}b`; controllability makes it a basis.
(2) In a suitable basis, `(A, b)` is in controllable canonical form. (3) Prove
`charpoly (companion c) = X^n + Σ cᵢ Xⁱ` by Laplace expansion along the last row, or induction.
(4) Feedback changes only the last row. (5) Transport back by similarity. An alternative is to
prove Ackermann's formula directly, `k = −eₙᵀ 𝒞⁻¹ p(A)`, but that still needs (3).

**Risks.** Companion charpoly determinant computations over `Fin n` are notoriously painful.
Basis changes between `Reachability`'s linear-map world and matrices add friction. This is a
genuinely new contribution (it's in neither Mathlib nor LeanForControl), but it's a multi-PR effort.

**Estimate.** 400–700 lines. Large. Suggested split: (a) companion matrix charpoly,
(b) the Krylov basis is a basis under controllability, (c) the placement theorem.

## #9 Eight-point algorithm: E determined up to scale

**Statement.** Given 8 correspondences `(x₁ᵢ, x₂ᵢ)`, let `M : Matrix (Fin 8) (Fin 3 × Fin 3) K` with
`M i (a, b) = x₂ᵢ a * x₁ᵢ b`. If `rank M = 8`, then for any `E ≠ 0` satisfying all eight
constraints, every `E'` satisfying them is `c • E`.

**Mathlib API.** `Matrix.rank` (= `finrank (range mulVecLin)`),
`LinearMap.finrank_range_add_finrank_ker` (FiniteDimensional/Lemmas.lean:173),
`finrank_eq_one_iff_of_nonzero'` / `exists_smul_eq_of_finrank_eq_one`
(FiniteDimensional/Basic.lean:561–602), `Matrix.dotProduct_mulVec`, `Fintype.sum_prod_type`.

**Proof sketch.** Identify `E` with `vec E : Fin 3 × Fin 3 → K` (`Matrix.of` / uncurry). Then
`x₂ᵀ E x₁ = (M *ᵥ vec E) i` by `sum_prod_type`. Rank–nullity gives `finrank ker = 9 − 8 = 1`, and
any two nonzero vectors in a 1-dimensional space are proportional. Corollary: if the true
essential matrix `[t]ₓR` is nonzero, it is the unique solution up to scale.

**Risks.** Low. The main friction is the `Fin 3 × Fin 3` vectorisation and getting
`finrank (Fin 3 × Fin 3 → K) = 9` via `simp`. An honest docstring must note that this is the
linear-algebra core only: no noise, no SVD, and no rank-2 projection.

**Estimate.** 60–100 lines. Small–medium. **Third most tractable.**

---

## Three new targets that add to the conversation

These aren't in Mathlib, LeanForControl or `docs/roadmap.md`. I checked by grep; "small gain" and
"triangulation" have no hits in Mathlib outside category theory.

1. **Discrete-time small-gain theorem (applied math / controls).** Two causal operators
   `G₁, G₂ : (ℕ → E) → (ℕ → E)` with finite ℓ∞ gains `γ₁, γ₂` (with bias) and `γ₁γ₂ < 1`: the feedback
   interconnection `e₁ = u₁ − G₂ e₂`, `e₂ = u₂ + G₁ e₁` is well-posed (by causality, define
   by recursion) and finite-gain stable, with explicit gain `γ₁/(1 − γ₁γ₂)`. It uses only
   `NormedAddCommGroup`, `ciSup` and induction. **~150–200 lines, medium.** It's the foundation for
   robust-control results and is absent from every Lean repo surveyed.

2. **Two-view triangulation: depths are unique (vision).** In the setting of
   `Epipolar.epipolar_constraint`, if `d₂ x₂ = R (d₁ x₁) + t` and `x₂ × (R x₁) ≠ 0` (the rays aren't
   parallel), then `(d₁, d₂)` is unique, with the closed form
   `d₁ = −((x₂ × t) · (x₂ × R x₁)) / ‖x₂ × R x₁‖²`. Add a cheirality corollary: a positive-depth
   solution determines the sign of `t` given `E` (the 4-fold ambiguity reduces to 1). It uses
   `Matrix.cross_*` lemmas already in Mathlib. **~80–120 lines, small.** It pairs naturally with #9.

3. **Steady-state α–β filter and the Kalata relation (estimation).** For the constant-velocity
   model with white-acceleration noise, the steady-state Kalman gains `(α, β)` satisfy
   `β = 2(2 − α) − 4√(1 − α)` and `α²/(1 − α)` equals a function of the tracking index
   `λ = σ_w T²/σ_v`. This is the 2×2 analogue of `ScalarKalman.steadyState`. Scalarising the 2×2 DARE
   by hand is the work. **~200–300 lines, medium.** Engineers use it daily, and it's a stepping
   stone towards the roadmap's DARE item without needing the general matrix DARE.

## Phase 2 outcome

- Picked **#6** as the most tractable unclaimed issue (small, entirely real-analytic, and it reuses
  existing lemmas).
- Implemented `ControlsLean/Estimation/RiccatiConvergence.lean` (headline:
  `tendsto_riccati_iterate`, `abs_riccati_iterate_sub_le`, `tendsto_gain_riccati_iterate`).
- `scripts/check.sh <file>` and the full `scripts/check.sh` both pass in `~/lean-work/ControlsLean`
  and on the branch in the worktree (32 audited theorems, standard axioms only).
- Branch `claude/controls-riccati-convergence` (worktree `~/lean-work/ctrl-claude-controls`),
  draft PR https://github.com/IamMikeHelsel/ctrl/pull/10, comment posted on issue #6.
