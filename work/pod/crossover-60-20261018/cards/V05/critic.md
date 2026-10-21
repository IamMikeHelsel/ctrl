# V05 independent critique

The useful result is an ambiguity-aware acquisition gate. A certified optimum alone does not identify the intended registration. The exact examples below isolate that distinction and supply a small test for choosing an additional observation. No TEASER implementation or physical acquisition was run.

## Independent checks

`critic_fixture.py` independently reconstructs the six labelled pairs using exact rational arithmetic. The two noncollinear groups admit identity and translation by (10,0,0), both proper rigid maps and both with TLS cost 3 at threshold 1. Every cross-group source distance is below 7/4 while the target distance is at least 9. For a rigid map, two residuals below 1 cannot cross groups. Thus at most three residuals are unsaturated, proving the continuous global lower bound 3 rather than merely comparing proposed poses.

The same lower bound survives unknown positive scale: for scale at most 4, the cross-group contradiction remains; for scale greater than 4, two within-group residuals below 1 are impossible, giving cost at least 4. Equality at cost 3 forces three exact correspondences from one group, which determine scale 1 and one proper rigid pose. This yields exactly two proper minimizers; permitting reflections yields four. The final classification uses a hand-derived geometric argument; the kernel results establish the lower bound and attainment, not this entire classification.

`critic_pm.py` checks all nine six-pair and twelve seven-pair cross constraints, all declared poses, and root's seventh correspondence. Adding (0,0,2) mapped to itself creates four affinely independent identity anchors. Equality forces these four exact matches, hence identity, even among orthogonal maps. The anchor determinant is 2. The equality-to-anchor step is hand-derived; the separate Lean anchor theorem proves that an isometry fixing those anchors is identity. Neither statement establishes acquisition truth or correspondence authenticity.

Meaningful mutations pass: raising the TLS threshold to 7.5 makes midpoint translation cost 8/3, invalidating the old bound 3; changing the seventh target to (10,0,2) changes identity and translated costs to 4 and 3. A reflected tetrahedron preserves every pair distance but admits no exact proper rigid fit. Collinear support admits different proper rotations. A scaled tetrahedron needs a declared scale parameter: 2I is not a rotation.

`critic_support.py` uses its own rational Gaussian elimination and enumerates every noncollinear triple, independently matching every producer pose and support. The original reflected-tetrahedron fixture has **four**, not two, proper three-support fits. An off-axis fifth point leaves one four-support proper fit; an on-axis fifth point leaves two. Completeness holds because every relevant exact support in these fixtures contains a noncollinear triple, and each such triple determines one proper rigid map. This does not establish completeness for noisy continuous pose sets. Allowing O(3) adds a reflection; removing correspondence labels gives twelve regular-tetrahedron proper poses instead of one.

Across all four exact hypotheses and all six prediction pairs, the 57-point virtual query pool has unique maximizer (-1,-1,-1), minimum squared separation 8. The initial query (0,2,1) scores 4; the readout (0,2,0) lies within radius 1 of two predictions. The best query's radius-1 balls are disjoint. At radius sqrt(2), a closest-pair midpoint defeats strict discrimination. These conclusions require the complete exact hypothesis list, a reliable new observation, unchanged fault assumptions, and a feasible physical query. They do not transfer automatically to noisy prior observations.

## Formal and literature boundaries

Independent Lean replay accepts 19 printed declarations: domain_fixture 8, domain_scale 7, pm_anchors 2, pm_query 2. The query module proves separation and disjoint radius-one readout balls for four declared vectors; critic_query_binding.json independently checks that these vectors match the reconstructed poses. Candidate completeness remains the exact geometric/enumeration bridge described above. Their closures contain only propext, Classical.choice and Quot.sound. Domain scale imports a fixture olean compiled independently into critic_replay. Logs and SHA-256 source bindings in critic_lean_replay.json are critic-owned. No original challenge statement changed. The earlier anchor replay ran before the corrected producer file and failed; the final frozen file passed.

The [TEASER paper](https://arxiv.org/html/2001.07715v2) certifies its rotation subproblem under stated inputs; its rank condition can also establish quaternion uniqueness up to sign. It explicitly discusses adversarial copied clouds. Our same-rotation translation ambiguity does not refute those results. Fixed-correspondence certificates also do not certify an arbitrary correspondence search. This is an exact diagnostic and acquisition experiment, not a novelty claim.

## Decision and next test

**GO** for a bounded ambiguity-aware query selector using complete hypotheses, all-pair separation, and an acquisition-feasibility mask. **NO-GO** for inferring a unique true-world registration from objective optimality or a pair-distance clique alone. **HOLD** for noisy-prior continuous covers, actual TEASER integration, and physical acquisition/provenance guarantees.

`critic_next_gate.json` proposes twenty semantic mutations and positive controls for the next authorized block; it does not claim that block has run. Require set-valued output when the evidence remains ambiguous. The three critic Python scripts pass scoped Ruff and execute with exact arithmetic; no repository integration or full repository qualification was performed by this critic.

Quality: 4/5 for a reproducible initial-session diagnostic with explicit model boundaries. Confidence is subjective: high for the exact fixtures and independently compiled statements, conditional for the geometric classification bridges, and unassessed for real sensor acquisition.
