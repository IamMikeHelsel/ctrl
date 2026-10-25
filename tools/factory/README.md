# ctrl proofs through the local 44 factory

This adapter reuses **44's existing `core/loop.py` unchanged**. It prepares a new,
sealed workspace with five independently scheduled proof-body tasks. The existing
60-idea campaign is indexed in `work/factory/20261021/idea-index.json`; indexing
does not complete its reviews or resume its timers.

The Mac authors exact statements and reviews evidence. Sparky runs the installed
local model and Linux bubblewrap acceptance. The model can return only the allowed
proof text file. The protected checker inserts that body into `solution : statement`,
compiles it, and checks the printed dependency axioms against `propext`,
`Classical.choice`, and `Quot.sound`. It rejects escape hatches and warnings.

The supervisor uses the existing cooperative `donut-host.lock`, checks idle GPU
and memory, and loads only an already installed model when no model is resident.
It never switches another resident model, downloads, uses cloud inference, or
changes the original ctrl checkout on Sparky. GPU cooldown resumes preserve the
factory's three-attempt limit. A nonparticipating external client is outside the
cooperative lock's guarantee. The budget is checked between attempts; an in-flight
model call can exceed it, bounded by the factory's HTTP timeout.

Python commands use `uv`; all remote transport goes through `ctrl.spark.ssh` and
`tools/spark/factory.sh`. There is no new daemon or alternate SSH configuration.

```sh
# Pick a NEW name for each changed contract/controller version.
uv run python tools/factory/prepare.py /Users/mike/Dev/44-runs/ctrl-proofs-NEW \
  --factory /Users/mike/Dev/44
uv run python tools/factory/dispatch.py upload ctrl-proofs-NEW \
  --workspace /Users/mike/Dev/44-runs/ctrl-proofs-NEW
uv run python tools/factory/dispatch.py init ctrl-proofs-NEW
uv run python tools/factory/dispatch.py run ctrl-proofs-NEW \
  --model gpt-oss:120b --minutes 25
uv run python tools/factory/dispatch.py status ctrl-proofs-NEW
uv run python tools/factory/dispatch.py fetch ctrl-proofs-NEW \
  --workspace /Users/mike/Dev/44-runs/ctrl-proofs-NEW-results
```

Use a new fetch destination to preserve previous snapshots. Check task states,
per-attempt compiler logs, exact prompts/responses, and `seal.json`; process exit
alone is not proof acceptance. Raw prompts/responses stay in the private run
workspace outside ctrl. A passing helper is not approval of an Erdős Challenge,
novelty, an original source theorem, an executable controller, or physical safety.
These five helpers currently import Mathlib, not the original campaign modules.
For another idea, supply `prepare.py --contracts /absolute/reviewed-contracts.json`.
Use the same schema as `contracts.json`, with one to five tasks and unique proof
paths. A new reviewed contract and a new workspace are required for every batch;
the remaining inventory entries are explicitly waiting for this step.

Integrated pilot lemmas live in `lean/Research/FactoryProofs.lean`. Run Lean commands
from the pinned project directory: `cd lean && lake build Research.FactoryProofs`.
Using `lake -d lean` from the repo root still lets elan select the root/default
toolchain and can produce incompatible dependency artifacts. The verified local
model contribution, repaired drafts, and independently authored proofs are listed
separately in `work/factory/20261021/integration-ledger.json`.

Validation: `uv run pytest -q tests/test_factory_proofs.py`. Live preflight also
compiles all frozen statements, accepts a true control, rejects a false control,
and checks isolation from host SSH files, writable acceptance, and host loopback.
