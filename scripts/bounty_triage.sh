#!/usr/bin/env bash
# List Erdős problems in formal-conjectures that are marked solved but have no Lean proof,
# shortest statement first. Usage: scripts/bounty_triage.sh [N]   (default 30)
set -euo pipefail
N="${1:-30}"
FC="${FC_DIR:-$HOME/lean-work/formal-conjectures}"
if [[ ! -d "$FC" ]]; then
  git clone -q --depth 1 https://github.com/google-deepmind/formal-conjectures.git "$FC"
else
  git -C "$FC" pull -q --ff-only || true
fi
echo "formal-conjectures @ $(git -C "$FC" rev-parse --short HEAD)"
for f in $(rg -l 'category research solved' "$FC/FormalConjectures/ErdosProblems"); do
  rg -q '\bsorry\b' "$f" || continue
  printf '%6d  %s\n' "$(wc -l < "$f")" "$(basename "$f" .lean)"
done | sort -n | head -n "$N" | awk '{printf "%5s lines  Erdős #%s  https://www.erdosproblems.com/%s\n", $1, $2, $2}'
