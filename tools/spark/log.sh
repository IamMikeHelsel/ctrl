#!/usr/bin/env bash
# ctrl spark log JOB [-f] [-n LINES]: print a job's log.txt (last 200 lines by default).
# -f follows until the job leaves the running state. Exit 5 if the job does not exist.
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=SCRIPTDIR/env.sh
source "$here/env.sh"
[[ $# -ge 1 ]] || { echo "usage: log.sh JOB [-f] [-n LINES]" >&2; exit 2; }
id="$1"; shift
follow=0; lines=200
while [[ $# -gt 0 ]]; do
  case "$1" in
    -f) follow=1; shift ;;
    -n) lines="${2:?}"; shift 2 ;;
    *) echo "usage: log.sh JOB [-f] [-n LINES]" >&2; exit 2 ;;
  esac
done
[[ "$id" =~ ^[A-Za-z0-9._-]+$ && "$lines" =~ ^[0-9]+$ ]] || { echo "bad job id or -n" >&2; exit 2; }
job="$CTRL_JOBS/$id"
[[ -f "$job/log.txt" ]] || { echo "job not found: $id" >&2; exit 5; }

running() {
  local tm
  tm="$(python3 -c 'import json,sys; m=json.load(open(sys.argv[1])); print(m.get("tmux","") if m.get("status") in ("running","starting") else "")' "$job/meta.json" 2>/dev/null)"
  [[ -n "$tm" ]] && tmux has-session -t "$tm" 2>/dev/null
}

if (( follow == 0 )); then exec tail -n "$lines" "$job/log.txt"; fi
tail -n "$lines" -f "$job/log.txt" &
tailpid=$!
trap 'kill $tailpid 2>/dev/null' EXIT
while running; do sleep 2; done
sleep 1
