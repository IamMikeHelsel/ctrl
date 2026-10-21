#!/usr/bin/env bash
# Ultra-fast pre-screening filter for JSP / Erdős bounty candidate problems.
#
# Filters out:
#   1. Any problem with open or merged pull requests on TheJustinSunPrize/awards.
#   2. Any problem already present in plby/lean-proofs (Boris Alexeev) or similar public repos.
#   3. Any problem marked with an existing Lean proof in the JSP catalog.
#
# Usage:
#   scripts/bounty_fast_filter.sh [OPTIONS] [FILE | JSP_ID ...]
#
# Examples:
#   scripts/bounty_fast_filter.sh                                   # Screen all Solved problems in jsp.json
#   scripts/bounty_fast_filter.sh -s all                            # Screen all problems in jsp.json (Open + Solved)
#   scripts/bounty_fast_filter.sh docs/assessments/SHORTLIST.md     # Screen problems mentioned in a file
#   scripts/bounty_fast_filter.sh docs/assessments/jsp_solved_no_lean_2026-10-17.json
#   scripts/bounty_fast_filter.sh JSP-000078 JSP-000264 JSP-001059 # Screen specific IDs
#   echo "JSP-000078 JSP-001059" | scripts/bounty_fast_filter.sh   # Screen from stdin
#   scripts/bounty_fast_filter.sh -v                                # Verbose mode (show rejection reasons)
#   scripts/bounty_fast_filter.sh --json                            # Output surviving shortlist as JSON
#   scripts/bounty_fast_filter.sh --ids-only                        # Output only surviving JSP IDs
#   scripts/bounty_fast_filter.sh -r                                # Refresh PR and plby cache from GitHub
#
# Options:
#   -s, --status STATUS   Filter catalog status: 'solved' (default), 'open', or 'all'
#   -v, --verbose         Print detailed rejection reason for each filtered problem
#   --strict              Also reject problems with closed/withdrawn awards PRs (zero competition)
#   --json                Output surviving shortlist as JSON array
#   --markdown, -m        Output table as GitHub markdown
#   --ids-only            Output only surviving JSP IDs (space- or newline-separated)
#   -r, --refresh         Refresh snapshots from TheJustinSunPrize/awards and plby/lean-proofs
#   -h, --help            Show this help message

set -euo pipefail
export PATH="/opt/homebrew/bin:/usr/local/bin:/usr/bin:/bin:${PATH:-}"
export LC_ALL="${LC_ALL:-en_US.UTF-8}"

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SNAP="${SNAPSHOT_DIR:-$REPO/data/snapshots}"
mkdir -p "$SNAP"

AWARDS_SNAP="$SNAP/awards_prs.json"
PLBY_SNAP="$SNAP/plby_erdos.json"

# Check if -r or --refresh is among arguments
REFRESH=0
PY_ARGS=()

for arg in "$@"; do
  if [[ "$arg" == "-r" || "$arg" == "--refresh" ]]; then
    REFRESH=1
  else
    PY_ARGS+=("$arg")
  fi
done

if [[ $REFRESH -eq 1 || ! -f "$AWARDS_SNAP" || ! -f "$PLBY_SNAP" ]]; then
  echo "Refreshing cache snapshots from GitHub..." >&2
  WORK="$(mktemp -d "${TMPDIR:-/tmp}/bounty_filter.XXXXXX")"
  trap 'rm -rf "$WORK"' EXIT

  # 1. Fetch awards PRs via gh if available
  if command -v gh >/dev/null 2>&1; then
    echo "  Fetching pull requests from TheJustinSunPrize/awards via gh..." >&2
    gh pr list --repo TheJustinSunPrize/awards --state all --limit 5000 \
      --json number,title,state,headRefName > "$WORK/prs.json" 2>/dev/null || true
  fi

  # 2. Fetch plby tree via GitHub API
  echo "  Fetching file tree from plby/lean-proofs..." >&2
  curl -sSfL --max-time 60 "https://api.github.com/repos/plby/lean-proofs/git/trees/main?recursive=1" \
    > "$WORK/plby_tree.json" 2>/dev/null || true

  python3 - "$SNAP" "$WORK" <<'PY_REFRESH'
import sys, os, json, re, datetime

snap_dir, work_dir = sys.argv[1], sys.argv[2]
now = datetime.datetime.now().astimezone().isoformat(timespec="seconds")

# Update awards PRs if fetched
prs_file = os.path.join(work_dir, "prs.json")
if os.path.exists(prs_file) and os.path.getsize(prs_file) > 10:
    try:
        raw_prs = json.load(open(prs_file))
        clean_prs = [{
            "number": p["number"],
            "title": p.get("title", ""),
            "state": p.get("state", "").upper(),
            "head": p.get("headRefName", "")
        } for p in raw_prs]
        with open(os.path.join(snap_dir, "awards_prs.json"), "w") as f:
            json.dump({"source": "TheJustinSunPrize/awards", "updated": now, "total_prs": len(clean_prs), "prs": clean_prs}, f, indent=1)
        print(f"  Saved {len(clean_prs)} awards PRs to snapshots.")
    except Exception as e:
        print(f"  Warning: failed to process fetched PRs: {e}", file=sys.stderr)

# Update plby if fetched
plby_file = os.path.join(work_dir, "plby_tree.json")
if os.path.exists(plby_file) and os.path.getsize(plby_file) > 10:
    try:
        tree = json.load(open(plby_file)).get("tree", [])
        nums = sorted(list({int(m.group(1)) for item in tree if (m := re.match(r"^src/latest/ErdosProblems/Erdos(\d+)\.lean$", item.get("path", "")))}))
        if nums:
            with open(os.path.join(snap_dir, "plby_erdos.json"), "w") as f:
                json.dump({"source": "plby/lean-proofs", "updated": now, "total_erdos_solved": len(nums), "solved_erdos": nums}, f, indent=1)
            print(f"  Saved {len(nums)} plby solved Erdős problems to snapshots.")
    except Exception as e:
        print(f"  Warning: failed to process plby tree: {e}", file=sys.stderr)

PY_REFRESH
fi

exec python3 "$REPO/scripts/bounty_fast_filter.py" --snapshot-dir "$SNAP" ${PY_ARGS[@]+"${PY_ARGS[@]}"}
