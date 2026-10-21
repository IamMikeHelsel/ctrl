# M06 domain review

AI-written; inherited root model, exact runtime identifier unavailable. The target is an **arbitrary bipartition** with internal edges e(S)+e(V\S) ≤ 2n²/47. It is not a balanced sparse-half claim. Source: frozen grade-01.txt and round-summary.txt listed in CARD.md. The source's hand neighborhood argument covers r=2m/n²≥49/125; fair random cut covers r≤8/47. Its middle-density BCL certificate was not recovered. No approved source or challenge was edited.

Primary status checked: [Balogh–Clemen–Lidický, Max Cuts in Triangle-free Graphs, arXiv2103.14179](https://arxiv.org/abs/2103.14179) explicitly states the existing n²/23.5 bound. Thus reproducing a faithful independent certificate is the objective; neither the constant nor max-cut local search is claimed novel. This abstract does not provide the missing local proof artifact, and no exhaustive literature novelty review was performed.

## Variance and local motifs

For a triangle-free graph, S=N(v) is independent and its crossing count C_v=Σ_{u∈N(v)}deg(u). Therefore Σ_v C_v=Σ_u deg(u)². If σ²=(1/n)Σ_u(deg(u)−2m/n)², some cut has internal/n² ≤ r/2−r²−σ²/n². This strengthens the original bound exactly by normalized degree variance. A sufficient gate is σ²/n²≥r/2−r²−2/47; its maximum demanded variance is15/752, attained at r=1/4. These graph averaging identities are hand derivations; the conditional scalar gate and maximum are kernel checked in domain_cut.lean. They leave all regular middle-density graphs untreated.

A materially different test allows an independent flip set outside S. Set g_u=deg(u)−2|N(u)∩S|. For arbitrary T disjoint from S,

    cross(S∪T)−cross(S)=Σ_{u∈T}g_u−2e(T).

For independent T, gains add with no penalty. Choosing T={u∈N(w)\N(v):g_u>0} is a faithful two-root motif in a triangle-free graph. domain_cut.lean proves the actual finite-edge Boolean identity and its sum; domain_penalty.lean proves the arbitrary-T identity including its essential penalty. The endpoint-incidence sum's regrouping into graph degrees is hand-bound, not falsely described as a SimpleGraph library theorem. No balanced-side restriction is inserted.

## Exact discriminating tests

`uv run --no-project --python /usr/local/bin/python3 python work/pod/crossover-60-20261018/cards/M06/domain_motif.py`

The script constructs graphs independently, verifies triangle-freeness and every prescribed root-pair's actual edge cut against the gain identity, and enumerates all cuts modulo complement. Petersen (n10,m15,r3/10): neighborhood internal6, improved motif internal4, actual optimum internal3. Clebsch (4-bit vertices, adjacency Hamming distance1 or4; n16,m40,r5/16): neighborhood internal15, best improved motif internal11, actual optimum internal8. Both have zero degree variance. Clebsch's motif value exceeds the target by exactly5/12032. The counterexample concerns the certificate family, not the theorem.

`domain_pair_extension.py` tests11760 candidates formed by arbitrary subsets of two extra neighborhoods, including the correct internal-edge penalty. Best cross remains29. More strongly, **every one of the2048 supersets of N(0)** has crossing count≤29. The XOR translation v↦v⊕a preserves adjacency and maps N(0) to N(a); hence retaining any entire neighborhood on one side cannot meet the target on this graph. The all-superset enumeration is exact Python, not a Lean certificate. A positive max-cut witness still gives crossing32.

Structural explanation: outside N(0), the root has gain−5; the remaining ten vertices induce Petersen and have gain1. Optimizing Σg−2e(T) is equivalent to an independent-set optimization: deleting a vertex incident to an internal edge improves |T|−2e(T) by at least1. Petersen has independence number4. This explanation and XOR transport are hand arguments, independently testable; no unproved universal inequality is inferred from tiny graphs.

## Consequence and next test

NO-GO for variance alone or any algorithm that freezes a full neighborhood on one side and only adds vertices. A viable next motif must allow **splitting the seed neighborhood**, or adopt a genuinely different cut construction. The precise next test is an induced-motif/cut-distribution certificate admitting such splits and explicitly passing uniform Clebsch blow-ups; a fixed sample-size residual would still need uniform error control before epsilon descent can apply. The existing source's missing middle-density BCL premise remains missing.

Evidence: exact finite integer tests; conditional/general cut-algebra Lean lemmas; hand graph semantics/transport; published target status. No universal middle-density proof, no solver-only acceptance, no new sparse-half constant. Quality18/20 (90%): strong falsification and faithful next action, incomplete global certificate. Subjective confidence high in the finite obstruction, not a calibrated probability of closing the theorem.

## Final acceptance supplements

`domain_moment.lean` checks the finite centered-moment identity and existence of a vertex whose normalized crossing count is at least r²+variance. Its inputs are an explicit mean equation, exact graph crossing-sum equation, and variance definition; the triangle-free graph counting needed to instantiate the crossing equation remains hand-derived. Together the three domain Lean files contain nine accepted declarations, only standard axioms. `push_neg` triggers a deprecation warning in the moment file, not a proof failure.

The frozen-neighborhood obstruction survives a uniform k-fold Clebsch blow-up: fixing its neighbor classes to one cut side leaves a cut objective multi-affine in the remaining class fractions. Iteratively choosing an endpoint of each affine coordinate never decreases the cut, so a maximum has whole classes assigned to sides. The16-vertex bound therefore gives cross≤29k² and internal≥11k², with r5/16 unchanged. This rounding/graph transport is a hand proof, not a checked universal blow-up theorem.

Independent critique: critic separately confirmed all256 two-root cases, all2048 supersets and the outside independence number4. Domain independently compiled critic_local.lean's four declarations: cube cut counts, normalized bad local cut, and conditional finite-radius blow-up inequalities. Those algebraic inequalities explicitly assume the graph gain estimate; they do not silently prove it. Log: domain_critic_local.log.

Scoped Ruff checks and formatting pass for both new Python files. Producer exact scripts were rerun after formatting. Repository-wide checks are root-owned at campaign handoff; no integrated repository changes were made by this role.
