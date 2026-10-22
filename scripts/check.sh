#!/usr/bin/env bash
# Build the library (or one file) and fail on any sorry/admit/axiom escape hatch.
# Usage: scripts/check.sh                  # whole library (build + axiom audit)
#        scripts/check.sh path.lean        # single file, fast iteration
#        scripts/check.sh --fast [path]    # fast check (skips lake build & audit)
set -euo pipefail
[[ -f "$HOME/.elan/env" ]] && source "$HOME/.elan/env"
cd "$(dirname "$0")/.."

# Safeguard against unpopulated cache / missing .lake symlink
source scripts/ensure_cache.sh
ensure_lake_cache "$(pwd)"

fast_mode=0
target_file=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    -f|--fast)
      fast_mode=1
      shift
      ;;
    -h|--help)
      cat << 'EOF'
Usage:
  scripts/check.sh                     # Full build, sorry check, and axiom audit
  scripts/check.sh <file.lean>         # Check single file with 'lake env lean'
  scripts/check.sh --fast [file.lean]  # Fast check without full library lake build

Options:
  -f, --fast     Skip 'lake build' and axiom audit; elaborate directly
  -h, --help     Show this help message
EOF
      exit 0
      ;;
    *)
      if [[ -z "$target_file" ]]; then
        target_file="$1"
      else
        echo "Error: Unexpected argument: $1" >&2
        exit 1
      fi
      shift
      ;;
  esac
done

if [[ -n "$target_file" ]]; then
  echo "Checking $target_file..."
  lake env lean "$target_file"
  files=("$target_file")
elif [[ "$fast_mode" -eq 1 ]]; then
  files=($(find ControlsLean -name '*.lean'))
  echo "Fast check on ${#files[@]} files..."
  for f in "${files[@]}"; do
    lake env lean "$f"
  done
else
  echo "Running full lake build..."
  lake build 2>&1 | grep -v "^✔" || true
  lake build >/dev/null
  files=($(find ControlsLean -name '*.lean'))
fi

if ! uv run --no-project python scripts/check_tokens.py "${files[@]}"; then
  echo "FAIL: escape hatch found" >&2
  exit 1
fi

if [[ -z "$target_file" && "$fast_mode" -eq 0 ]]; then
  # Lean wraps long `#print axioms` lines; join continuation lines first.
  audit=$(lake env lean scripts/Audit.lean | awk '
    /^'\''/ { if (l != "") print l; l = $0; next }
    { sub(/^[ \t]+/, " "); l = l $0 }
    END { if (l != "") print l }')
  ax='(propext|Classical\.choice|Quot\.sound)'
  if echo "$audit" | grep -vE "^'.*' (depends on axioms: \[ ?($ax(, ?$ax)*)? ?\]|does not depend on any axioms)$" | grep .; then
    echo "FAIL: nonstandard axioms" >&2
    exit 1
  fi
  echo "$audit" | wc -l | xargs echo "Axiom audit passed for headline theorems:"
fi

echo "OK: ${#files[@]} file(s) checked, no forbidden proof escapes"
