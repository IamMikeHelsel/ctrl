#!/usr/bin/env bash
# Invoked by tools/factory/dispatch.py through ctrl.spark.ssh, never whole-repo rsync.
set -euo pipefail
run=$1
action=$2
[[ "$run" =~ ^ctrl-proofs-[a-zA-Z0-9-]+$ ]] || exit 2
factory_run="$HOME/44-runs/$run"
[[ -d "$factory_run/control" ]] || exit 2
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"
export FORTYFOUR_WORKSPACE="$factory_run"
cd "$factory_run"
case "$action" in
  init)
    uv run --no-project python - "$factory_run" <<'PY'
import json, pathlib, subprocess, sys
root=pathlib.Path(sys.argv[1])
project=pathlib.Path.home()/'lean-work/ctrl/lean'
chain=pathlib.Path(subprocess.check_output(['elan','which','lean'],cwd=project,text=True).strip()).parent.parent
lean_path=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=project,text=True).strip()
runtime={'lean_project':str(project),'toolchain':str(chain),'lean_path':lean_path}
target=root/'reference/runtime.json'
with target.open('x') as f: json.dump(runtime,f,indent=2)
PY
    uv run --no-project python control/loop.py init
    ;;
  preflight) uv run --no-project python control/supervise.py --preflight-only ;;
  run) uv run --no-project python control/supervise.py --model "$3" --minutes "$4" ;;
  status)
    uv run --no-project python - <<'PY'
import json,pathlib
root=pathlib.Path.cwd()
queue=json.loads((root/'queue-state.json').read_text())
journal=json.loads((root/'state.json').read_text())
if journal.get('task_id') in queue: queue[journal['task_id']]=journal
print(json.dumps({'tasks':queue,'journal':journal},indent=2))
PY
    ;;
  *) exit 2 ;;
esac
