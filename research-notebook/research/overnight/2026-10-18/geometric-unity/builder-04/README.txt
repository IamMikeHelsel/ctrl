Complex matrix scalar extension and adjoint bridge
Builder gate, 18 October 2026 UTC

Owns only geometric-unity/builder-04. Independent acceptance is required.
The target is actual complex scalar extension of the accepted real exterior
representation and the preserved GUComplex.bar. It is not a physics claim.

The three new proof modules are ComplexEquivalence, ComplexBridge and
ComplexControls. Seventeen inherited modules match builder-03 byte-for-byte.
ComplexAdjoint matches complex-adjoint-04/builder byte-for-byte. The old sibling
AdjointControls from that separate gate is not imported; this avoids the known
module-name collision without changing either frozen file.

Run verify.py from this folder or by absolute path. It uses the existing pinned
lean-controls dependency project, rebuilds every local module into cache/fresh-01,
audits all local declarations, tests separate false clients, and runs leanchecker.
A nonempty fresh output directory is rejected; preserve previous attempts before
starting a deliberately new run. Dependency caches remain trusted inputs.

Run check_complex.py for the exact Gaussian-integer regression check. That check
is finite and is not a proof of the general theorem. proof-guide.txt explains the
actual Lean chain and its limits. NEXT-GATE.txt states a possible next proof.

Development failures and logs are preserved under attempts. compile.py is only
a development helper and can use development products. The fresh verifier does
not use either that cache or the local project's build products. The final
SHA256SUMS excludes cache products; it includes sources, logs and recorded checks.
Root owns repository sync, commits, push and manuscript integration.
