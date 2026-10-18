ROBUST SAMPLED AXIS — standalone benchmark contract

model.json records the exact mathematical verification task and links each
semantic component to the frozen Lean source hashes. It is structured metadata,
not an executable semantics definition. Independent implementations should
compare their own dynamics and timing conventions with the stated equations.
The Lean model-to-certificate identities are the checked semantic connection.

Reproduce proofs using ../README.txt and the source archive it identifies.
The whole-project verification checks the polynomial certificates and actual
ODE correspondence; a trace simulation alone does not satisfy acceptance.

Important modeling details
- r is fixed over an execution; controller gains stay unchanged as it varies.
- Both e and d are held. d enters AFTER clipping but INSIDE the rate multiplier.
- Only the clipped component is limited to1; the combined drive may exceed1.
- All state coordinates are continuous; derivatives at switching times are not
  required. The command uses the trajectory's own sample state.
- The initial set couples position, velocity and acceleration. Starting merely
  inside the position interval does not meet this initial condition.
- The positive uniform minimum dwell excludes accumulation of infinitely many
  samples before a finite time. No particular numerical scheduler is verified.

Useful attempted refutations / adaptations
1. Replacing the middle rate Bernstein coefficient with the midpoint plant
   must fail the existing model identity. This is tested in the artifact.
2. Removing r from the actual acceleration ODE must fail the existing exact
   solution bridge. This is tested in the artifact.
3. The wider sector[1/4,1] cannot use this same P for nonnegative infinitesimal
   dissipation. The exact obstruction is checked in UncertaintyScope.lean.
4. A coarse response norm estimate loses this sufficient error budget, while
   direct quadratic response energy succeeds. The diagnostic is recorded at
   ../../research/application/uncertainty-ablation/response-ablation.json.
These are certificate boundaries, not general unsafe-plant conclusions.

The source package is a local working artifact. No project release license has
been selected. Dependencies retain their own licenses. No affiliation or
institutional endorsement is implied by this benchmark.
