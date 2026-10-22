#!/usr/bin/env bash
# Build and fail on sorry/admit/axiom escape hatches. Usage: scripts/audit.sh [Module.Name ...]
set -euo pipefail
source "$HOME/.elan/env"
cd "$(dirname "$0")/.."
lake build "$@" 2>&1 | grep -vE '^(✔|⚠ .*linter)' || true
lake build "$@" >/dev/null
if grep -rnE '\b(sorry|admit)\b|^axiom ' ErdosLab; then echo "FAIL: escape hatch in ErdosLab/" >&2; exit 1; fi
echo "OK"
