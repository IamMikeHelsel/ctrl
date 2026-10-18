Bounded fixed-controller uncertainty feasibility spike, 2026-10-17.
The main lean-controls project and frozen publication are read-only inputs.

From workspace root:
  PYTHONPATH="$PWD/.tools/research-python/lib/python3.14/site-packages" .tools/travel-plot-python/bin/python research/opportunity-assessment/scratch-lag-uncertainty/feasibility.py
  PYTHONPATH="$PWD/.tools/research-python/lib/python3.14/site-packages" .tools/travel-plot-python/bin/python research/opportunity-assessment/scratch-lag-uncertainty/tight_sector.py
  python3 research/opportunity-assessment/scratch-lag-uncertainty/replay.py

The first exact attempt uses the old broad sector and intentionally fails2/12
producer checks. Its surviving10 source files are UNVERIFIED exploratory output.
The tight-sector subfolder is the successful revised attempt:12 checked sources.
Both numeric grids are diagnostics, not proofs. They use existing Python3.12
NumPy and pure-Python SymPy1.14 from the research environment; no environment was
changed and no package was installed. The exact producer is imported read-only.

From lean-controls:
  ELAN_HOME="$PWD/../.tools/elan" ../.tools/elan/bin/lake env lean "$PWD/../research/opportunity-assessment/scratch-lag-uncertainty/RateEnclosure.lean"

No project .olean is produced by these scratch commands. Existing main-project
and pinned mathlib imports are cached dependencies for the checks. This is not a
fresh independent Lean/mathlib build. The report and manifests distinguish:
1 numeric exploration;2 exact rational preparation;3 checked vertex/bridge lemmas;
4 the unassembled proposed whole-trajectory theorem.

The public names in RateEnclosure.lean belong to LagUncertaintySpike and are not
imported into the main artifact. The generated matrix sources independently use
LeanControls.Generated.UncertainA* namespaces in isolated Lean invocations.
There is no assembled aggregate claiming an uncertain trajectory theorem.
