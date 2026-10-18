INDEPENDENT REVIEW OF MOTION BUILDER 05

Read REPORT.txt and result.json for the decision after this folder is frozen.
Review ownership is limited to this folder. No builder, manuscript, shared state,
repository, toolchain pin or external service was changed.

review.py rebuilds all 15 local modules into a new cache, audits every local
declaration, and replays each module with leanchecker. It reuses only pinned
public dependency products. Sources and all old evidence are preserved.
ReviewClients.lean adds independent generic and exact concrete challenge clients.
negative_review.py requires explicit False goals and rejects wrong-error passes.
exact_review.py independently evaluates rational FIR derivative extrema, the
sufficient velocity test, finite selection, structural identity, and clocks.
run_clients.py exercises the original translator on six fixed JSON cases, then
rebuilds their generated proofs against the independent fresh proof products.
It also runs a controlled input-replacement test for the wrapper's recorded hash.
audit_clients.py audits the reviewer module and each generated client module.

The old wrapper race is preserved as evidence. It does not invalidate the fixed
source proof or the six stable-input results. Root is preparing a separate
snapshotting wrapper; that new wrapper needs its own review.

Attempt 01 preserves two reviewer-side rational-to-real elaboration errors.
They were repaired only in the review clients. They were not counted as negative
controls and did not require a change to the builder proof.
