Actual matrix units for the split Clifford spinor action
18 October 2026 UTC

This folder closes the real matrix-representation gate. Its target is the
specific splitAction built in analyst-01. The proof works on Mathlib's actual
exterior subset basis. It does not assume a matrix model with the desired laws.

Main result:
  HyperbolicSpinor.splitMatrixEquiv :
    GUClifford.Cl ≃ₐ[ℝ] Matrix (Finset (Fin 7)) (Finset (Fin 7)) ℝ

The matrix index has 128 elements. GUClifford.Cl is the real Clifford algebra of
Q(v)=sum of seven positive squares minus seven negative squares.

Read report.txt for scope, proof-guide.txt for the exact construction, and
NEXT-GATE.txt for what remains. verification.json and logs/ record the builder
self-check. Independent acceptance must come from the next critic folder.
SHA256SUMS freezes all files except cache/ and the manifest itself.

To reproduce, copy this folder to a sibling scratch folder and run its verify.py.
Do not run verify.py in the frozen evidence folder: it rewrites logs. The copied
script must remain at the same directory depth so it finds the workspace pins.

The verifier reuses the pinned Lean 4.35.0 and pinned prebuilt Mathlib dependencies.
It recompiles all 13 local modules into a fresh temporary directory, audits
public declarations, runs leanchecker, and tests clients that must pass or fail.
The .olean files under cache/ are development products, not preserved evidence.

No previous frozen source, shared paper, Git state or remote was edited.
