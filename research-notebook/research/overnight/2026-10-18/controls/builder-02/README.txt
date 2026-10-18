Constant-bias terminal hold — builder milestone 02

Read report.txt for the claim and its limits. The original goal c and holding
controller stay unchanged. The shifted equilibrium is an analysis identity.

Reproduce from the research workspace:
  python3 research/overnight/2026-10-18/controls/builder-02/dev.py
  python3 research/overnight/2026-10-18/controls/builder-02/verify.py

The development helper caches local objects. The verifier rebuilds the complete
local source closure in a new temporary directory. It reuses pinned Mathlib
objects, audits all public local statements, runs separate kernel replays and
rejects three concrete false statements. Accepted witnesses show why each
false statement fails. Build caches and bytecode are not frozen artifacts.

Main source entry points:
  ConstantBias.input_shift
  ConstantBias.physical_bounds
  BiasFixtures.two_second_actual
  BiasFixtures.two_second_endpoint
  DirectBias.fixed_reference_then_bias_hold
  DirectBias.fixed_reference_bias_endpoint

All names are under LeanControls. BiasWitness contains exact resting and moving
physical examples, plus wrong-sign, double-counting and missing-offset checks.

source-freeze.json binds all local proof sources and the verifier scripts.
artifact-sha256.json binds this package's reports, source, scripts and evidence.
parent-preservation-before.json and parent-preservation-after.json check that
all accepted builder-01 artifacts remained unchanged. Independent review is a
separate gate. Root owns repository storage and any publication decision.
