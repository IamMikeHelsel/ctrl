Definition audit 02 — frozen analyst package

Read candidate-ledger.txt for the source boundary, declared model, derivation,
negative controls, and one next formal proof gate. Read source-map.json and
source-refresh.json for the source evidence and live retrieval hashes.

Exact reproducible checks, with only Python's standard library:
  python3 exact_candidate.py
  python3 basis_gate.py
  python3 fock_realization.py
  python3 gauge_domain_gate.py
Run from this directory, or pass each script's path from another directory.
Each script prints JSON and fails on a failed check. The corresponding retained
*_results.json files record this analyst's successful runs.

The basis check covers 3185 explicit algebraic-curvature basis tensors. It is
finite exact evidence. It is not a Lean proof or an independent implementation
of the stated Clifford algebra. A fresh grader must review the basis argument
and arithmetic semantics, not only run the scripts.

The recommended next gate is K_R=-scal times 1 in actual Mathlib Cl(7,7),
including the Bianchi hypothesis and the non-Bianchi four-form counterexample.
No author identification or full GU claim is part of that gate.

No accepted source was edited. No Git action or author contact occurred.
Notebook preservation and independent grading belong to the coordinator.
