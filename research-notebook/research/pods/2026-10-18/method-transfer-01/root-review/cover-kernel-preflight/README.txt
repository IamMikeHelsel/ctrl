CLOSED COMPUTATION COST TEST — NOT A COVERAGE PROOF
18 October2026,18:48UTC.

The generator selects16 E5 moment cells with the longest saved rational
endpoint strings, ordered by original node index on ties. It recomputes the
two interval upper bounds in Lean using exact rationals and proves that
both are nonpositive. Its interval divisions are guarded by the closed
cell-domain check; no generic soundness theorem is provided here.

Fresh Lean4.35 compile: exit0,0.819s.
Separate leanchecker replay: exit0,2.740s.
All16 theorem closures use only propext, Classical.choice and Quot.sound.
Source and logs are in attempt-184831/. The input certificate hash is pinned
in run.py and result.json. There were no failed attempts or leftover jobs.

This deterministic sample shows that closed kernel arithmetic is feasible
for these cells. It gives no performance distribution or full-run bound.
It leaves interval soundness, all872 leaves, partition coverage, exterior
intervals and graph integration open. Independent acceptance is not claimed.
