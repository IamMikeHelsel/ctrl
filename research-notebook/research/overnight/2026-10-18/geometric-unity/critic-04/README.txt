Independent reviewer workspace for builder-04 complex matrix equivalence.
Root owns repository sync and shared paper integration.

review_lean.py rebuilds every frozen local source and adds independent clients,
checks local axiom dependencies, challenges false clients and runs leanchecker.
The final default replay uses a new cache/fresh-03 directory. The recorded run
used fresh-02, then --continue after reviewer-client repairs. The 21 unchanged
source products were checked against source hashes before continuation.
audit_full_closure.py supplies the explicit all-module audit for that run; it
includes the otherwise unimported OrderControls module. The main runner now
imports all modules explicitly, so a new full replay includes that check.
review_exact.py uses Gaussian integers and an independent tuple-wedge coordinate
implementation. It imports no builder code and uses no floating-point numbers.
check_preservation.py verifies nine pinned manifests and the inherited sources.

Frozen candidate: builder-04/SHA256SUMS
SHA256: 861cd093c525217d7f9f04dbee0ff22889efd541e746bc7a82eeea9a20c4a8c9
Toolchain: Lean4.35.0, eb6cafb7290e8bd5f2937522d8d804f58f02bafc.
Mathlib: 56a005855ea17e0b0958f73ec801ae140b0a1679.

The scripts use pinned prebuilt third-party dependency products. All local proof
sources are rebuilt in the review cache. A fresh local build is not a verified
bootstrap of the compiler, library cache, operating system or hardware.

Failures in attempts/ are retained. No candidate source or earlier evidence was
edited. See report.txt and decision.json for the final decision and exact scope.
