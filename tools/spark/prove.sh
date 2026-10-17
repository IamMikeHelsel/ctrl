#!/usr/bin/env bash
# ctrl spark prove NNN [--minutes M] [--model leanstral] [--attempts K]
# Env: PROVE_REASONING=high|none (Leanstral thinking, default high), PROVE_MAX_TURNS (default 150).
# Sets up a job (scratch copy of the repo, shared Lake packages), starts prove-run.sh in tmux,
# prints {"job": ID} and exits. The job keeps going in tmux session "ctrl-ID".
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=SCRIPTDIR/env.sh
source "$here/env.sh"

usage() { echo "usage: prove.sh NNN [--minutes M] [--model MODEL] [--attempts K]" >&2; exit 2; }
[[ $# -ge 1 && "$1" =~ ^[0-9]+$ ]] || usage
nnn="$1"; shift
minutes=60; model=leanstral; attempts=3
while [[ $# -gt 0 ]]; do
  case "$1" in
    --minutes) minutes="${2:?}"; shift 2 ;;
    --model) model="${2:?}"; shift 2 ;;
    --attempts) attempts="${2:?}"; shift 2 ;;
    *) usage ;;
  esac
done
[[ "$minutes" =~ ^[0-9]+$ && "$attempts" =~ ^[0-9]+$ && "$minutes" -ge 1 && "$attempts" -ge 1 ]] || usage
[[ "$model" =~ ^[A-Za-z0-9._:/-]+$ ]] || usage

src="$CTRL_REPO/lean"
sol="ErdosLab/Erdos$nnn.lean"
[[ -f "$src/$sol" ]] || { echo "no $sol in $src; run ctrl spark sync" >&2; exit 1; }
[[ -f "$src/Challenge/Erdos$nnn.lean" ]] || { echo "no Challenge/Erdos$nnn.lean in $src" >&2; exit 1; }
[[ -d "$src/.lake/packages" ]] || { echo "no $src/.lake/packages; run lake exe cache get there" >&2; exit 1; }
command -v tmux >/dev/null || { echo "tmux missing" >&2; exit 1; }
command -v claude >/dev/null || { echo "claude missing" >&2; exit 1; }
curl -sf "$OLLAMA_URL/api/show" -d "{\"model\":\"$model\"}" >/dev/null \
  || { echo "ollama model $model not available at $OLLAMA_URL" >&2; exit 1; }

# Optional knobs (env, recorded in meta.json because tmux does not pass the caller's environment):
reasoning="${PROVE_REASONING:-high}"; max_turns="${PROVE_MAX_TURNS:-150}"
[[ "$reasoning" == high || "$reasoning" == none ]] || { echo "PROVE_REASONING must be high or none" >&2; exit 2; }
[[ "$max_turns" =~ ^[0-9]+$ ]] || { echo "PROVE_MAX_TURNS must be an integer" >&2; exit 2; }

id="$(new_job_id "$nnn" prove)"
job="$CTRL_JOBS/$id"
mkdir -p "$job/outputs"
: > "$job/log.txt"
meta_set "$job/meta.json" job "$id" nnn "$nnn" kind prove started "$(now_iso)" status starting \
  model "$model" budget "json:{\"minutes\": $minutes, \"attempts\": $attempts}" tmux "ctrl-$id" \
  reasoning "$reasoning" max_turns "json:$max_turns"

# Scratch copy with the repo layout check.py expects (lean/ and work/NNN/). Only those two: Claude
# Code loads CLAUDE.md/AGENTS.md/.claude/ from parent dirs, and the prompt carries the rules itself.
scratch="$job/scratch"
mkdir -p "$scratch/work"
rsync -a --exclude .lake "$src/" "$scratch/lean/"
[[ -d "$CTRL_REPO/work/$nnn" ]] && rsync -a --exclude candidates "$CTRL_REPO/work/$nnn/" "$scratch/work/$nnn/"
# Lake: packages are shared via symlink (Mathlib is ~5 GB). prove-run.sh builds Challenge in $src
# and then copies $src/.lake/build into the scratch, so the scratch never writes to $src's build.
mkdir -p "$scratch/lean/.lake"
ln -s "$src/.lake/packages" "$scratch/lean/.lake/packages"
# The statement is frozen: make Challenge/ read-only so an agent edit fails loudly.
chmod -R a-w "$scratch/lean/Challenge" "$scratch/lean/Challenge.lean"
cp "$scratch/lean/$sol" "$job/outputs/original.lean"

meta_set "$job/meta.json" status running
tmux new-session -d -s "ctrl-$id" \
  "bash $(printf %q "$here/prove-run.sh") $(printf %q "$job") >> $(printf %q "$job/log.txt") 2>&1"
printf '{"job": "%s"}\n' "$id"
