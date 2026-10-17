#!/usr/bin/env bash
# Build the library (or one file) and fail on any sorry/admit/axiom escape hatch.
# Usage: scripts/check.sh            # whole library
#        scripts/check.sh path.lean  # single file, fast iteration
set -euo pipefail
source "$HOME/.elan/env"
cd "$(dirname "$0")/.."

if [[ $# -gt 0 ]]; then
  lake env lean "$1"
  files=("$1")
else
  lake build 2>&1 | grep -v "^✔" || true
  lake build >/dev/null
  files=($(find ControlsLean -name '*.lean'))
fi

if grep -nE '\b(sorry|admit)\b|^axiom ' "${files[@]}"; then
  echo "FAIL: escape hatch found" >&2
  exit 1
fi
if [[ $# -eq 0 ]]; then
  audit=$(lake env lean scripts/Audit.lean)
  if echo "$audit" | grep -vE "^'.*' depends on axioms: \[propext, Classical.choice, Quot.sound\]$" | grep .; then
    echo "FAIL: nonstandard axioms" >&2
    exit 1
  fi
  echo "$audit" | wc -l | xargs echo "Axiom audit passed for headline theorems:"
fi
echo "OK: ${#files[@]} file(s) checked, no sorry/admit/axiom"
