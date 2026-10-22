# Sourced by the tools/spark scripts. Non-login SSH shells on the Spark lack ~/.local/bin and elan.
# shellcheck shell=bash
export PATH="$HOME/.local/bin:$HOME/opt/bin:$HOME/.elan/bin:$PATH"
# shellcheck disable=SC1091
[[ -f "$HOME/.elan/env" ]] && source "$HOME/.elan/env"

CTRL_REPO="${CTRL_REPO:-$HOME/lean-work/ctrl}"
CTRL_JOBS="${CTRL_JOBS:-$HOME/lean-work/jobs}"
SOLVE_PY="${SOLVE_PY:-$HOME/venvs/solve/bin/python}"
OLLAMA_URL="${OLLAMA_URL:-http://127.0.0.1:11434}"

# Point headless Claude Code at the Spark's Ollama (Anthropic-compatible /v1/messages).
# Usage: ollama_claude_env MODEL [CONTEXT_TOKENS]
ollama_claude_env() {
  local model="$1" ctx="${2:-65536}"
  unset ANTHROPIC_API_KEY CLAUDE_CODE_USE_BEDROCK CLAUDE_CODE_USE_VERTEX
  export ANTHROPIC_BASE_URL="$OLLAMA_URL" ANTHROPIC_AUTH_TOKEN=ollama
  export ANTHROPIC_MODEL="$model" ANTHROPIC_SMALL_FAST_MODEL="$model"
  export ANTHROPIC_DEFAULT_HAIKU_MODEL="$model" ANTHROPIC_DEFAULT_SONNET_MODEL="$model"
  export ANTHROPIC_DEFAULT_OPUS_MODEL="$model"
  export CLAUDE_CODE_MAX_CONTEXT_TOKENS="$ctx" CLAUDE_CODE_AUTO_COMPACT_WINDOW="$ctx"
  export CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC=1
  # Claude Code otherwise appends a <total_tokens> system message after every tool result.
  export CLAUDE_CODE_TOTAL_TOKENS_REMINDER=off
  export DISABLE_AUTOUPDATER=1 DISABLE_TELEMETRY=1 DISABLE_ERROR_REPORTING=1
  # Local models are slow on big prompts; the default 10 min request timeout is too tight.
  export API_TIMEOUT_MS="${API_TIMEOUT_MS:-1800000}"
  # A private config dir: no user skills/plugins/CLAUDE.md/MCP from ~/.claude (they cost ~7k prompt
  # tokens and Leanstral loops on the Skill tool), and prove sessions stay out of ~/.claude/projects.
  export CLAUDE_CONFIG_DIR="${CTRL_CLAUDE_CONFIG_DIR:-$HOME/.config/ctrl-prove-claude}"
  mkdir -p "$CLAUDE_CONFIG_DIR"
}

# Update fields of a meta.json atomically: meta_set FILE key value [key value ...]
# Values are stored as strings; prefix with "json:" to store parsed JSON (numbers, objects, null).
meta_set() {
  local file="$1"; shift
  python3 - "$file" "$@" <<'PY'
import json, os, sys
path, kv = sys.argv[1], sys.argv[2:]
meta = json.load(open(path)) if os.path.exists(path) else {}
for k, v in zip(kv[::2], kv[1::2]):
    meta[k] = json.loads(v[5:]) if v.startswith("json:") else v
tmp = path + ".tmp"
with open(tmp, "w") as f:
    json.dump(meta, f, indent=2)
    f.write("\n")
os.replace(tmp, path)
PY
}

new_job_id() {  # new_job_id NNN KIND -> 20261017-153012-1216-prove-a1b2
  printf '%s-%s-%s-%s' "$(date -u +%Y%m%d-%H%M%S)" "$1" "$2" "$(head -c2 /dev/urandom | od -An -tx1 | tr -d ' \n')"
}

now_iso() { date -u +%Y-%m-%dT%H:%M:%SZ; }
