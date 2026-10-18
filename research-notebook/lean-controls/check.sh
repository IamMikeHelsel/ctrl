#!/bin/sh
set -eu
cd "$(dirname "$0")"
if [ -z "${ELAN_HOME:-}" ] && [ -x "$PWD/../.tools/elan/bin/lake" ]; then
  export ELAN_HOME="$PWD/../.tools/elan"
fi
if [ -z "${LAKE:-}" ]; then
  if [ -x "${ELAN_HOME:-$HOME/.elan}/bin/lake" ]; then
    LAKE="${ELAN_HOME:-$HOME/.elan}/bin/lake"
  else
    LAKE=lake
  fi
fi
mkdir -p evidence
python3 scripts/sync_audit.py --check
"$LAKE" build > evidence/build.log 2>&1
cat evidence/build.log
"$LAKE" env lean Audit.lean > evidence/axioms.log 2>&1
cat evidence/axioms.log
python3 scripts/check_audit.py
