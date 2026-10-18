Treating the Tremors We Built into Robots

Editable research note. main.tex is the main document. robustness.tex records
the separate irregular-noise gate and its execution boundary. The manuscript does not
claim publication readiness, a new FIR method, or a general solution to VLA jitter.

Figure 1 comes from comparison-04/figure/comparison.png. Figure 2 is the final
still from jerk-prefix-animation/jerk-prefix-still.png. The latter shows ideal
reference motion, not measured physical motion. The animation is 17 seconds.

The Lean certificate and first fixed numerical comparison have separate
independent computational reviews. The harder comparison passed canonical polynomial replay but failed two strict
native-clock checks. A separate native-state repair passed the original finite checks and independent
physical replay. The filter failures remain. Its tiny native phases also show
why command variation and physical motion need separate measures.
No threshold was relaxed. The full-method literature audit supports a specialized
formalization case study; it does not establish a new general control method.

AI assistance and actual human contributions are stated in the manuscript and
../contributions.txt. No paper has been submitted. This file is not a license.

Build with the local Tectonic binary from this project directory:
  ../../../.tools/tectonic/tectonic main.tex
The built-in Codex LaTeX project compiler can also check the saved main.tex.

Source ledger: sources.txt. Final artifact bindings, compilation, and eight-page
visual checks are recorded in verification.json. The final integration review
and native06 review have separate scopes. The portable proof bundle is at
../reviewer-bundle/. It requires an existing pinned Lean/mathlib environment.
