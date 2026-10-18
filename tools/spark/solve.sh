#!/usr/bin/env bash
# erdos spark solve NNN SCRIPT [args...]
# Runs ~/lean-work/ctrl/work/NNN/SCRIPT with ~/venvs/solve's python, solvers (~/opt/bin) on PATH,
# cwd = the job's outputs/ dir, inside tmux. Prints {"job": ID} and exits.
# Env: SOLVE_TIMEOUT_MIN (default 0 = no limit).
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=SCRIPTDIR/env.sh
source "$here/env.sh"

[[ $# -ge 2 && "$1" =~ ^[0-9]+$ ]] || { echo "usage: solve.sh NNN SCRIPT [args...]" >&2; exit 2; }
nnn="$1"; script="$2"; shift 2
[[ "$script" != /* && "$script" != *..* ]] || { echo "SCRIPT must be a path inside work/$nnn/" >&2; exit 2; }
path="$CTRL_REPO/work/$nnn/$script"
[[ -f "$path" ]] || { echo "no $path; run erdos spark sync" >&2; exit 1; }
[[ -x "$SOLVE_PY" ]] || { echo "no solver venv at $SOLVE_PY" >&2; exit 1; }
command -v tmux >/dev/null || { echo "tmux missing" >&2; exit 1; }
timeout_min="${SOLVE_TIMEOUT_MIN:-0}"
[[ "$timeout_min" =~ ^[0-9]+$ ]] || { echo "SOLVE_TIMEOUT_MIN must be an integer" >&2; exit 2; }

id="$(new_job_id "$nnn" solve)"
job="$CTRL_JOBS/$id"
mkdir -p "$job/outputs"
: > "$job/log.txt"
args_json="$(python3 -c 'import json,sys; print(json.dumps(sys.argv[1:]))' "$@")"
meta_set "$job/meta.json" job "$id" nnn "$nnn" kind solve started "$(now_iso)" status running \
  model json:null budget "json:{\"minutes\": $timeout_min}" script "$script" args "json:$args_json" tmux "ctrl-$id"

# The job body, run by tmux. Quoted with printf %q so arbitrary args survive.
body="source $(printf %q "$here/env.sh"); cd $(printf %q "$job/outputs");"
body+=" echo \"[\$(date -u +%H:%M:%S)] solve: $(printf %q "$script") $(printf '%q ' "$@")\";"
body+=" start=\$(date +%s);"
if (( timeout_min > 0 )); then body+=" timeout --kill-after=30 $(( timeout_min * 60 ))"; fi
body+=" $(printf %q "$SOLVE_PY") -u $(printf %q "$path") $(printf '%q ' "$@") < /dev/null; rc=\$?;"
body+=" case \$rc in 0) st=success;; 124|137) st=timeout;; *) st=failed;; esac;"
body+=" meta_set $(printf %q "$job/meta.json") status \$st exit_code json:\$rc finished \$(now_iso) elapsed_s json:\$(( \$(date +%s) - start ));"
body+=" echo \"[\$(date -u +%H:%M:%S)] exit \$rc (\$st)\""
tmux new-session -d -s "ctrl-$id" "bash -c $(printf %q "$body") >> $(printf %q "$job/log.txt") 2>&1"
printf '{"job": "%s"}\n' "$id"
