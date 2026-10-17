#!/usr/bin/env bash
# ctrl spark jobs: print every job's meta.json as one JSON array, newest first.
# A job whose meta says "running" but whose tmux session is gone is reported as "lost".
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=SCRIPTDIR/env.sh
source "$here/env.sh"
sessions="$(tmux list-sessions -F '#{session_name}' 2>/dev/null || true)"
python3 - "$CTRL_JOBS" "$sessions" <<'PY'
import json, pathlib, sys
root, sessions = pathlib.Path(sys.argv[1]), set(sys.argv[2].split())
jobs = []
for meta in root.glob("*/meta.json") if root.is_dir() else []:
    try:
        m = json.loads(meta.read_text())
    except (OSError, ValueError):
        m = {"job": meta.parent.name, "status": "unreadable"}
    if m.get("status") in ("running", "starting") and m.get("tmux") not in sessions:
        m["status"] = "lost"
    m["dir"] = str(meta.parent)
    jobs.append(m)
jobs.sort(key=lambda m: (m.get("started") or "", m.get("job") or ""), reverse=True)
print(json.dumps(jobs, indent=2))
PY
