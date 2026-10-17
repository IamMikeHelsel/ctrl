#!/usr/bin/env bash
# Semantic and type-based search in Lean 4 / Mathlib using Loogle.
# Queries the live Mathlib search index without requiring local compilation or indexing overhead.
#
# Usage:
#   scripts/loogle.sh "Matrix.PosDef"
#   scripts/loogle.sh "Real.sqrt _ * Real.sqrt _"
#   scripts/loogle.sh "(x : ℝ) : 0 < Real.exp x"
#   scripts/loogle.sh --limit 5 "Controllable"
#   scripts/loogle.sh --json "Continuous, Real.sin"

set -euo pipefail

LIMIT=10
RAW_JSON=0
MODULE_FILTER=""
QUERY=""

show_help() {
  cat << 'EOF'
Loogle Lean 4 / Mathlib Search Tool

Usage:
  scripts/loogle.sh [options] "<query>"

Options:
  -n, --limit <N>     Maximum number of results to display (default: 10)
  -m, --module <Mod>  Filter results by module prefix (e.g. "Mathlib.LinearAlgebra")
  -j, --json          Output raw JSON response from Loogle
  -h, --help          Show this help message

Query Syntax Examples:
  Exact/Prefix Name:    scripts/loogle.sh "Matrix.PosDef"
  Multiple Constants:   scripts/loogle.sh "Real.exp, 0 < _"
  Type / Equality:      scripts/loogle.sh "⊢ _ + 0 = _"
  Subterm Pattern:      scripts/loogle.sh "Real.sqrt _ * Real.sqrt _"
  Signature Pattern:    scripts/loogle.sh "(x : ℝ) : 0 < Real.exp x"
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -n|--limit)
      LIMIT="$2"
      shift 2
      ;;
    -m|--module)
      MODULE_FILTER="$2"
      shift 2
      ;;
    -j|--json)
      RAW_JSON=1
      shift
      ;;
    -h|--help)
      show_help
      exit 0
      ;;
    *)
      if [[ -z "$QUERY" ]]; then
        QUERY="$1"
      else
        QUERY="$QUERY $1"
      fi
      shift
      ;;
  esac
done

if [[ -z "$QUERY" ]]; then
  echo "Error: No search query provided. Use --help for usage." >&2
  exit 1
fi

API_URL="https://loogle.lean-lang.org/json"

# Perform HTTP request
RESPONSE=$(curl -sSG "$API_URL" --data-urlencode "q=$QUERY" --max-time 15)

if [[ -z "$RESPONSE" ]]; then
  echo "Error: Received empty response from Loogle server ($API_URL)." >&2
  exit 1
fi

if [[ "$RAW_JSON" -eq 1 ]]; then
  echo "$RESPONSE"
  exit 0
fi

if command -v jq >/dev/null 2>&1; then
  header=$(echo "$RESPONSE" | jq -r '.header // ""' 2>/dev/null || true)
  count=$(echo "$RESPONSE" | jq -r '.count // 0' 2>/dev/null || true)
  error=$(echo "$RESPONSE" | jq -r '.error // ""' 2>/dev/null || true)

  if [[ -n "$error" ]]; then
    echo "Loogle Error: $error" >&2
    exit 1
  fi

  if [[ -n "$header" ]]; then
    echo "$header"
  fi

  # Extract hits with optional module filter and limit
  echo "$RESPONSE" | jq -r \
    --arg mod "$MODULE_FILTER" \
    --argjson lim "$LIMIT" '
    .hits // []
    | if $mod != "" then map(select(.module | startswith($mod))) else . end
    | .[0:$lim][]
    | "• \(.name)\n  type:   \(.type | gsub("^[ \t\n]+"; ""))\n  module: \(.module)" +
      (if .doc then "\n  doc:    \(.doc | split("\n")[0])" else "" end) + "\n"
  '
else
  # Minimal fallback if jq is not installed
  echo "$RESPONSE"
fi
