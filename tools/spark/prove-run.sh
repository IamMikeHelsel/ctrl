#!/usr/bin/env bash
# Internal: the body of a prove job, run by prove.sh inside tmux. Usage: prove-run.sh JOB_DIR
# Loops up to K headless Claude Code attempts on the local model, checks after each, keeps outputs.
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=SCRIPTDIR/env.sh
source "$here/env.sh"
job="$1"; meta="$job/meta.json"; out_root="$job/outputs"
read -r nnn model minutes attempts reasoning max_turns < <(python3 -c '
import json,sys; m=json.load(open(sys.argv[1]))
print(m["nnn"], m["model"], m["budget"]["minutes"], m["budget"]["attempts"],
      m.get("reasoning", "high"), m.get("max_turns", 150))' "$meta")
src="$CTRL_REPO/lean"; scratch="$job/scratch"; lean="$scratch/lean"
sol="ErdosLab/Erdos$nnn.lean"; subdir="ErdosLab/Erdos$nnn"
start=$(date +%s); deadline=$(( start + minutes * 60 ))
log() { echo "[$(date -u +%H:%M:%S)] $*"; }

cleanup() {  # kill anything (lake serve, lean, MCP servers) still running inside the scratch dir
  local p cwd
  for p in /proc/[0-9]*; do
    cwd="$(readlink "$p/cwd" 2>/dev/null)" || continue
    [[ "$cwd" == "$scratch"* && "${p#/proc/}" != "$$" ]] && kill "${p#/proc/}" 2>/dev/null
  done
}
finish() {
  local status="$1"
  cleanup
  chmod -R u+w "$lean/Challenge" "$lean/Challenge.lean" 2>/dev/null  # so the job dir can be deleted
  cp "$lean/$sol" "$out_root/final.lean" 2>/dev/null
  [[ -d "$lean/$subdir" ]] && cp -r "$lean/$subdir" "$out_root/final-subdir"
  diff -u --label "a/lean/$sol" --label "b/lean/$sol" "$out_root/original.lean" "$lean/$sol" \
    > "$out_root/final.patch"
  meta_set "$meta" status "$status" finished "$(now_iso)" attempts_done "json:${k_done:-0}" \
    elapsed_s "json:$(( $(date +%s) - start ))"
  log "job finished: $status"
  exit 0
}
trap 'finish cancelled' INT TERM HUP

log "prove job $(basename "$job"): Erdos$nnn, model $model, ${minutes} min, $attempts attempts, reasoning $reasoning, max $max_turns turns/session"
# Bring the source copy's build up to date (serialised across jobs), then seed the scratch build dir.
( cd "$src" && flock "$src/.lake/ctrl-build.lock" lake build "Challenge.Erdos$nnn" ) || { log "lake build Challenge.Erdos$nnn failed in $src"; finish failed; }
rm -rf "$lean/.lake/build"; cp -a "$src/.lake/build" "$lean/.lake/build"

toolchain="$(cat "$lean/lean-toolchain")"
cat > "$job/mcp.json" <<EOF
{"mcpServers": {"lean-lsp": {"command": "lean-lsp-mcp", "args": ["--disable-tools", "lean_build"],
  "env": {"LEAN_PROJECT_PATH": "$lean"}}}}
EOF
ollama_claude_env "$model"
allowed='Read,Edit,Write,Glob,Grep,TodoWrite,Bash(lake env lean:*),Bash(lake build:*),mcp__lean-lsp__*'
denied='WebFetch,WebSearch,Task,Agent,Skill,SlashCommand,NotebookEdit,Bash(lake update:*),Bash(lake clean:*),Bash(lake exe:*)'
# $reasoning (high|none) reaches tools/spark/leanstral.jinja as a [ctrl:reasoning=...] marker in the
# system prompt; other models ignore it.
last_check=""; status=failed; k_done=0

# run_claude TIMEOUT PROMPT [extra claude args]: one headless Claude Code session on the local model.
# stream-json so the log shows each tool call live and a killed session still leaves a transcript.
# Run in the background + wait, so INT/TERM/HUP (tmux kill-session) are handled at once.
run_claude() {
  local t="$1" p="$2"; shift 2
  rm -f "$out/claude.json"
  ( cd "$lean" && timeout --kill-after=30 "$t" claude -p "$p" "$@" \
      --output-format stream-json --verbose --max-turns "$max_turns" \
      --mcp-config "$job/mcp.json" --strict-mcp-config \
      --permission-mode acceptEdits --allowedTools "$allowed" --disallowedTools "$denied" \
      --append-system-prompt "[ctrl:reasoning=$reasoning]" < /dev/null 2>> "$out/claude.stderr" \
      | python3 "$here/stream_filter.py" "$out/transcript.jsonl" "$out/claude.json"
    exit "${PIPESTATUS[0]}" ) &
  wait $!
  local rc=$?
  cleanup
  return "$rc"
}
ended_in_thinking() {  # true if the last assistant message has only thinking blocks
  python3 - "$1" <<'PY'
import json, sys
last = None
for line in open(sys.argv[1]):
    try:
        ev = json.loads(line)
    except ValueError:
        continue
    if ev.get("type") == "assistant":
        last = ev["message"].get("content") or []
sys.exit(0 if last and all(b.get("type") == "thinking" for b in last) else 1)
PY
}
summarize() {
  python3 - "$1" <<'PY' || true
import json, sys
try:
    r = json.load(open(sys.argv[1]))
    u = r.get("usage", {})
    print(f"  claude: {r.get('subtype')} error={r.get('is_error')} turns={r.get('num_turns')} "
          f"api_s={r.get('duration_api_ms', 0) / 1000:.0f} out_tokens={u.get('output_tokens')}")
    print("  result: " + (r.get("result") or "")[:600].replace("\n", " "))
except FileNotFoundError:
    print("  claude: no result event (session killed by its time slice); see transcript.jsonl")
except Exception as e:
    print(f"  claude.json unreadable: {e}")
PY
}

for (( k = 1; k <= attempts; k++ )); do
  remaining=$(( deadline - $(date +%s) ))
  if (( remaining < 60 )); then status=timeout; log "budget exhausted before attempt $k"; break; fi
  # Split what is left evenly over the attempts still to run, so later attempts (which get the
  # previous check's errors as feedback) are not starved by a first attempt that grinds.
  slice=$(( remaining / (attempts - k + 1) )); status=failed
  out="$out_root/attempt-$k"; mkdir -p "$out"
  if [[ -n "$last_check" ]]; then
    feedback=$'## Previous attempt\nThe file already contains the previous attempt'"'"$'s edits. Its check failed with:\n```\n'"$last_check"$'\n```\nStart from this report.'
  else feedback=""; fi
  python3 - "$here/prove_prompt.md" "$out/prompt.md" "$nnn" "$k" "$attempts" "$(( slice / 60 ))" \
    "$toolchain" "$feedback" "$lean" <<'PY'
import sys
src, dst, nnn, k, n, mins, tc, fb, lean = sys.argv[1:]
t = open(src).read()
for key, val in {"NNN": nnn, "ATTEMPT": k, "ATTEMPTS": n, "MINUTES_LEFT": mins,
                 "TOOLCHAIN": tc, "LAST_CHECK": fb, "LEAN_DIR": lean}.items():
    t = t.replace("{{" + key + "}}", val)
open(dst, "w").write(t)
PY
  log "attempt $k/$attempts: claude -p on $model, timeout ${slice}s (job has ${remaining}s left)"
  t0=$(date +%s); attempt_end=$(( t0 + slice ))
  run_claude "$slice" "$(cat "$out/prompt.md")"; rc=$?; k_done=$k
  # Leanstral sometimes emits its tool call inside an unclosed [THINK] block; llama.cpp then returns
  # it as thinking, Claude Code sees no tool_use and ends the session. Resume it with a nudge.
  nudges=0
  while (( rc == 0 && nudges < 8 )) && ended_in_thinking "$out/transcript.jsonl"; do
    left=$(( attempt_end - $(date +%s) ))
    (( left > 90 )) || break
    sid="$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1])).get("session_id",""))' "$out/claude.json" 2>/dev/null)"
    [[ -n "$sid" ]] || break
    nudges=$(( nudges + 1 ))
    log "  session ended inside a thinking block (tool call not executed); resume $nudges"
    run_claude "$left" "Your last message ended inside a thinking block, so its tool call was not executed. Continue the task: close your reasoning and emit the tool call." --resume "$sid"; rc=$?
  done
  summarize "$out/claude.json"
  log "  claude rc=$rc after $(( $(date +%s) - t0 ))s ($nudges resumes)"
  cp "$lean/$sol" "$out/"
  [[ -d "$lean/$subdir" ]] && cp -r "$lean/$subdir" "$out/"
  diff -u --label "a/lean/$sol" --label "b/lean/$sol" "$out_root/original.lean" "$lean/$sol" > "$out/diff.patch"
  if ! diff -rq "$src/Challenge" "$lean/Challenge" > "$out/challenge.diff" 2>&1; then
    log "  Challenge/ was modified; attempt rejected"; status=failed; break
  fi
  ( cd "$scratch" && timeout 1200 bash lean/scripts/check.sh "$nnn" --fast ) > "$out/check.json" 2> "$out/check.stderr" &
  wait $!; crc=$?; echo "$crc" > "$out/check.exit"
  log "  check --fast exit $crc"
  if (( crc == 0 )); then status=success; break; fi
  last_check="$( (cat "$out/check.json"; tail -c 3000 "$out/check.stderr") | head -c 4000)"
  if (( rc == 124 || rc == 137 )); then
    status=timeout; log "  attempt hit its time slice"
    (( deadline - $(date +%s) < 60 )) && break
  fi
done
finish "$status"
