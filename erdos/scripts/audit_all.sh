#!/usr/bin/env bash
# Run check.sh for every erdos/ErdosLab/Erdos*.lean and print a JSON array of the results.
# Exit 0 iff every problem passes, else 4. Usage: erdos/scripts/audit_all.sh [--fast]
set -uo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
status=0
first=1
printf '['
for f in "$here"/../ErdosLab/Erdos*.lean; do
  [ -e "$f" ] || continue
  nnn="$(basename "$f" .lean)"; nnn="${nnn#Erdos}"
  [[ "$nnn" =~ ^[0-9]+$ ]] || continue
  out="$("$here/check.sh" "$nnn" "$@")" || status=4
  [ $first -eq 1 ] || printf ','
  first=0
  printf '%s' "$out"
done
printf ']\n'
exit $status
