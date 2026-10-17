#!/usr/bin/env bash
# Build the `leanstral` Ollama model on the Spark.
#   bash ~/lean-work/ctrl/tools/spark/build-leanstral.sh [--reasoning high|none]
#
# Ollama 0.34 only accepts Go templates in a Modelfile TEMPLATE, but renders a GGUF's *embedded*
# jinja template through llama.cpp (that is what makes Mistral tool calls parse). The stock template
# rejects what Claude Code sends through Ollama's Anthropic shim (extra system messages, user turns
# right after tool results), so we write tools/spark/leanstral.jinja into a copy of the GGUF.
# Cost: ~72 GB extra in ~/models/leanstral plus Ollama's own blob copy; a few minutes on NVMe.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
reasoning=high
[[ "${1:-}" == "--reasoning" ]] && reasoning="${2:?high|none}"
src="$HOME/models/leanstral/Leanstral-1.5-119B-A6B-Q4_K_M.gguf"
dst="$HOME/models/leanstral/Leanstral-1.5-119B-A6B-Q4_K_M.ctrl.gguf"
expected_sha=8d7bdbfa733c3fcde4c9ce527ba3d4aa3a49af77e7767b3ed5ae649e6c92b902
export PATH="$HOME/.local/bin:$PATH"

[[ -f "$src" ]] || { echo "missing $src (see docs/machines.md for the download command)" >&2; exit 1; }
if [[ "${VERIFY_SHA:-0}" == 1 ]]; then
  echo "verifying sha256 of $src ..." >&2
  echo "$expected_sha  $src" | sha256sum -c - >&2
fi

tpl="$(mktemp --suffix .jinja)"
trap 'rm -f "$tpl"' EXIT
sed "s/{%- set REASONING = '[a-z]*' %}/{%- set REASONING = '$reasoning' %}/" "$here/leanstral.jinja" > "$tpl"
grep -q "set REASONING = '$reasoning'" "$tpl"

work="$(mktemp -d)"
trap 'rm -f "$tpl"; rm -rf "$work"' EXIT
cp "$tpl" "$work/chat_template.jinja"
(cd "$work" && uv run -q --no-project --with gguf gguf-new-metadata --force \
  --chat-template-file chat_template.jinja "$src" "$dst.tmp" >&2)
mv "$dst.tmp" "$dst"
ollama create leanstral -f "$here/Modelfile.leanstral" >&2
ollama show leanstral >&2
echo "{\"model\": \"leanstral\", \"gguf\": \"$dst\", \"reasoning\": \"$reasoning\"}"
