#!/usr/bin/env bash
# ctrl spark check NNN [--fast]: run the repo's check script in the Spark's rsync'd copy.
# stdout and the exit code are passed through unchanged (see docs/cli.md exit codes).
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=SCRIPTDIR/env.sh
source "$here/env.sh"
[[ $# -ge 1 && "$1" =~ ^[0-9]+$ ]] || { echo "usage: check.sh NNN [--fast]" >&2; exit 2; }
cd "$CTRL_REPO" || { echo "no repo copy at $CTRL_REPO; run ctrl spark sync" >&2; exit 1; }
[[ -f lean/scripts/check.sh ]] || { echo "missing $CTRL_REPO/lean/scripts/check.sh" >&2; exit 1; }
exec bash lean/scripts/check.sh "$@"
