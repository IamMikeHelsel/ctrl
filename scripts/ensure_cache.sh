#!/usr/bin/env bash
# Ensure .lake is a valid symlink or points to a populated Mathlib build cache.
# Prevents accidental re-download and re-compilation of Mathlib from scratch.
set -euo pipefail

ensure_lake_cache() {
  local project_root="${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
  local lake_dir="$project_root/.lake"
  local mathlib_pkg="$lake_dir/packages/mathlib"

  # Case 1: .lake exists and has mathlib package installed
  if [[ -d "$mathlib_pkg" ]]; then
    return 0
  fi

  # Case 2: Broken symlink
  if [[ -L "$lake_dir" && ! -e "$lake_dir" ]]; then
    echo "[cache_safeguard] Warning: .lake is a broken symlink pointing to '$(readlink "$lake_dir")'." >&2
    rm -f "$lake_dir"
  fi

  # Case 3: Empty or unpopulated directory
  if [[ -d "$lake_dir" && ! -L "$lake_dir" && ! -d "$mathlib_pkg" ]]; then
    # Check if directory is empty
    if [[ -z "$(ls -A "$lake_dir" 2>/dev/null)" ]]; then
      rmdir "$lake_dir"
    else
      local backup="${lake_dir}.unpopulated.$(date +%s)"
      echo "[cache_safeguard] Warning: .lake exists but lacks mathlib packages. Moving to $backup" >&2
      mv "$lake_dir" "$backup"
    fi
  fi

  # Attempt auto-discovery of existing populated cache in candidate paths
  local candidates=()

  # Worktree parent/common repo root
  local git_common
  if git_common=$(git -C "$project_root" rev-parse --git-common-dir 2>/dev/null); then
    local main_worktree
    main_worktree=$(cd "$project_root/$git_common/.." && pwd)
    if [[ "$main_worktree" != "$project_root" ]]; then
      candidates+=("$main_worktree/.lake")
    fi
  fi

  # Known canonical and sibling directories
  candidates+=(
    "/Users/mike/lean-work/ControlsLean/.lake"
    "$project_root/../ControlsLean/.lake"
    "$project_root/../ctrl/.lake"
  )

  local found_cache=""
  for cand in "${candidates[@]}"; do
    if [[ -d "$cand/packages/mathlib" ]]; then
      found_cache="$cand"
      break
    fi
  done

  if [[ -n "$found_cache" ]]; then
    echo "[cache_safeguard] Found populated cache at: $found_cache" >&2
    echo "[cache_safeguard] Auto-linking $lake_dir -> $found_cache" >&2
    ln -sfn "$found_cache" "$lake_dir"
    if [[ -d "$mathlib_pkg" ]]; then
      echo "[cache_safeguard] Cache restored successfully." >&2
      return 0
    fi
  fi

  # If not found and fresh build not explicitly authorized, abort with error
  if [[ "${ALLOW_FRESH_LAKE_BUILD:-0}" != "1" ]]; then
    cat >&2 << 'EOF'
========================================================================
FATAL: Lake cache safeguard triggered!
'.lake' is missing, unpopulated, or a broken symlink.
Running 'lake build' or 'lake env' without a valid cache will cause
Lake to re-download and re-compile Mathlib from scratch (~hours!).

To resolve this:
  1) Symlink to an existing populated cache:
       ln -s /Users/mike/lean-work/ControlsLean/.lake .lake
  2) Or if intentionally starting a fresh cache:
       lake exe cache get
  3) Or set ALLOW_FRESH_LAKE_BUILD=1 to override.
========================================================================
EOF
    exit 1
  fi
}

# Allow direct execution
if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
  ensure_lake_cache "${1:-$(cd "$(dirname "$0")/.." && pwd)}"
fi
