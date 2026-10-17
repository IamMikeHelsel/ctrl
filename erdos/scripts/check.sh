#!/usr/bin/env bash
# Run checks 1-4 of docs/erdos-lab/architecture.md for one problem and print ONE JSON object on stdout:
#   {"nnn", "build": {"ok","log"}, "tokens": {"ok","hits"}, "axioms": {"ok","axioms"},
#    "binding": {"ok","detail"}}
# Exit 0 iff all checks pass, 4 if any check failed, 2 on bad usage.
# Usage: erdos/scripts/check.sh NNN [--fast]   (any cwd)
#   --fast: build only the Challenge module with lake, compile the solution with `lake env lean`.
set -uo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
[ -f "$HOME/.elan/env" ] && source "$HOME/.elan/env"
cd "$here/.."
if ! command -v lake >/dev/null 2>&1; then
  echo '{"error": "lake not found on PATH (install elan)"}'
  exit 1
fi
exec python3 -I "$here/check.py" "$@"
