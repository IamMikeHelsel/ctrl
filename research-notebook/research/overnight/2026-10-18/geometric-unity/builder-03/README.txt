Actual real matrix adjoint — builder gate 03

Assigned 18 October 2026, deadline 08:50 UTC.
This folder owns only the new real adjoint gate. Earlier folders remain frozen.
Independent review is required before acceptance.

Input: critic-02 accepts builder-02's concrete real algebra equivalence.
Target: for the actual ordered exterior basis and the existing splitMatrixEquiv,
prove K^T=K, K^2=I and rho(star x)=K rho(x)^T K over the real Clifford algebra.
K is the ordered product of the seven actual negative generator matrices.
The star is Mathlib's real Clifford conjugation, reversing products and negating
vectors. Creation-transpose must be derived from the actual basis action.

The four new modules are TransposeBridge, VolumeForm, RealAdjoint and
AdjointControls. Thirteen inherited modules are copied byte-for-byte. The copies
make the fresh build closure explicit. Do not change their pins or contents.

Replay the builder check with:
  python3 verify.py
Run the exact integer convention check with:
  python3 check_conventions.py
The compiler is the workspace's pinned Lean 4.35.0 and Mathlib revision
56a005855ea17e0b0958f73ec801ae140b0a1679. Only pinned dependency products are
reused. The fresh check excludes the project cache and builds all local sources
in a new temporary directory, audits axioms and replays every module with the
separate leanchecker.

No complex representation, Hermitian signature proof, Phi selection, physical
prediction or publication novelty is claimed. The accepted source errata and
author questions in critic-01 remain authoritative. The 2021 draft already has
action (9.4). Do not replace its missing variational choices with guesses.
