#!/usr/bin/env bash
# Fast inner-loop scratch runner for testing isolated Lean 4 lemmas & snippets
# without recompiling the entire module graph or running full library audits.
#
# Usage:
#   scripts/scratch_check.sh scratch/test.lean
#   scripts/scratch_check.sh -c "import Mathlib; #check (1 : Nat)"
#   scripts/scratch_check.sh << 'EOF'
#   import Mathlib.Data.Real.Basic
#   lemma test (x : ℝ) : x + 0 = x := by simp
#   EOF
#
# Options:
#   -c, --code "<code>"     Check inline code snippet
#   -i, --import <Module>   Auto-prepend 'import <Module>'
#   -s, --strict            Fail if 'sorry' or 'admit' is present
#   -k, --keep              Keep scratch file after execution
#   -h, --help              Show usage help

set -euo pipefail
[[ -f "$HOME/.elan/env" ]] && source "$HOME/.elan/env"
cd "$(dirname "$0")/.."

# Ensure Lake build cache is intact and populated
source scripts/ensure_cache.sh
ensure_lake_cache "$(pwd)"

mkdir -p scratch

code_str=""
extra_import=""
strict_mode=0
keep_file=0
target_file=""
is_temp_file=0

cleanup() {
  if [[ "$is_temp_file" -eq 1 && "$keep_file" -eq 0 && -n "$target_file" && -f "$target_file" ]]; then
    rm -f "$target_file"
  fi
}
trap cleanup EXIT

while [[ $# -gt 0 ]]; do
  case "$1" in
    -c|--code)
      code_str="$2"
      shift 2
      ;;
    -i|--import)
      extra_import="$2"
      shift 2
      ;;
    -s|--strict)
      strict_mode=1
      shift
      ;;
    -k|--keep)
      keep_file=1
      shift
      ;;
    -h|--help)
      cat << 'EOF'
Usage:
  scripts/scratch_check.sh [options] [file.lean]
  scripts/scratch_check.sh [options] -c "lean code"
  scripts/scratch_check.sh [options] < file.lean

Options:
  -c, --code "..."       Evaluate inline code snippet
  -i, --import <Mod>     Auto-prepend 'import <Mod>' to snippet
  -s, --strict           Fail on 'sorry' / 'admit' (default permits for scratchpad exploration)
  -k, --keep             Keep generated temporary scratch file in scratch/
  -h, --help             Show this help message

Examples:
  scripts/scratch_check.sh scratch/my_lemma.lean
  scripts/scratch_check.sh -i ControlsLean.Controls.Hurwitz2 -c "#check ControlsLean.Controls.IsHurwitz2"
  scripts/scratch_check.sh << 'EOF'
  import Mathlib.Analysis.SpecialFunctions.Pow.Real
  lemma test_pow (x : ℝ) : x ^ 1 = x := by ring
  EOF
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

# If code was passed via -c
if [[ -n "$code_str" ]]; then
  target_file="scratch/scratch_$(date +%s)_$$.lean"
  is_temp_file=1
  if [[ -n "$extra_import" ]]; then
    echo "import $extra_import" > "$target_file"
  fi
  echo "$code_str" >> "$target_file"
# If no file was passed, read from stdin (if stdin is not a terminal)
elif [[ -z "$target_file" ]]; then
  if [[ -t 0 ]]; then
    echo "Error: No file or code provided. See --help." >&2
    exit 1
  fi
  target_file="scratch/scratch_$(date +%s)_$$.lean"
  is_temp_file=1
  if [[ -n "$extra_import" ]]; then
    echo "import $extra_import" > "$target_file"
  fi
  cat >> "$target_file"
else
  if [[ ! -f "$target_file" ]]; then
    echo "Error: File not found: $target_file" >&2
    exit 1
  fi
fi

start_time=$(date +%s)
echo "Elaborating $target_file..."

if lake env lean "$target_file"; then
  end_time=$(date +%s)
  duration=$((end_time - start_time))

  # Check for escape hatches (sorry/admit)
  sorry_count=$(grep -cE '\b(sorry|admit)\b' "$target_file" || true)

  if [[ "$sorry_count" -gt 0 ]]; then
    if [[ "$strict_mode" -eq 1 ]]; then
      echo "FAIL: Elaboration passed, but contains $sorry_count sorry/admit in strict mode." >&2
      exit 1
    else
      echo "✓ Elaboration SUCCEEDED in ${duration}s (contains $sorry_count sorry/admit escape hatch(es))."
    fi
  else
    echo "✓ Elaboration SUCCEEDED in ${duration}s (clean proof, no sorry/admit)."
  fi
else
  exit_code=$?
  echo "✗ Elaboration FAILED (exit code $exit_code)." >&2
  exit "$exit_code"
fi
