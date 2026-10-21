#!/usr/bin/env python3
"""
Ultra-fast pre-screening filter for JSP / Erdős bounty candidate problems.

Filters out:
  1. Any problem with open or merged pull requests on TheJustinSunPrize/awards.
  2. Any problem already present in plby/lean-proofs (Boris Alexeev) or similar public repos.
  3. Any problem marked with an existing Lean proof in the JSP catalog.
"""

import sys, os, json, re, argparse

def main():
    parser = argparse.ArgumentParser(
        description="Ultra-fast pre-screening filter for JSP / Erdős bounty candidate problems."
    )
    parser.add_argument(
        "candidates", nargs="*",
        help="Candidate problems (file path, raw JSON, JSP IDs like JSP-000078, or stdin)"
    )
    parser.add_argument(
        "-s", "--status", default="solved", choices=["solved", "open", "all"],
        help="Filter candidate problems by catalog status: 'solved' (default), 'open', or 'all'"
    )
    parser.add_argument(
        "-v", "--verbose", action="store_true",
        help="Print detailed rejection reasons for filtered candidates"
    )
    parser.add_argument(
        "--strict", action="store_true",
        help="Also reject problems with closed/withdrawn awards PRs (strict zero-competition mode)"
    )
    parser.add_argument(
        "--json", action="store_true",
        help="Output surviving shortlist as JSON array"
    )
    parser.add_argument(
        "-m", "--markdown", action="store_true",
        help="Output table as GitHub markdown"
    )
    parser.add_argument(
        "--ids-only", action="store_true",
        help="Output only surviving JSP IDs"
    )
    parser.add_argument(
        "--snapshot-dir", default=None,
        help="Path to snapshots directory (default: <repo>/data/snapshots)"
    )

    args = parser.parse_args()

    repo_dir = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
    snap_dir = args.snapshot_dir or os.environ.get("SNAPSHOT_DIR") or os.path.join(repo_dir, "data/snapshots")

    # Snapshot files
    awards_path = os.path.join(snap_dir, 'awards_prs.json')
    plby_path = os.path.join(snap_dir, 'plby_erdos.json')
    map_path = os.path.join(snap_dir, 'jsp_erdos_map.json')
    jsp_path = os.path.join(snap_dir, 'jsp.json')

    awards_doc = json.load(open(awards_path)) if os.path.exists(awards_path) else {}
    plby_doc = json.load(open(plby_path)) if os.path.exists(plby_path) else {}
    map_doc = json.load(open(map_path)) if os.path.exists(map_path) else {}
    jsp_catalog = json.load(open(jsp_path)).get('entries', {}) if os.path.exists(jsp_path) else {}

    plby_erdos = set(plby_doc.get('solved_erdos', []))
    jsp_to_erdos = {k: set(v) for k, v in map_doc.get('mappings', {}).items()}

    # Index awards PRs
    prs = awards_doc.get('prs', [])
    pr_data = {} # jid -> {'open': [], 'merged': [], 'closed': [], 'plby': bool}

    for pr in prs:
        num = pr['number']
        title = pr.get('title', '')
        branch = pr.get('head', '')
        state = pr.get('state', '').upper()
        jids = {f"JSP-{int(j):06d}" for j in re.findall(r'JSP-(\d+)', title, re.IGNORECASE) + re.findall(r'jsp-(\d+)', branch, re.IGNORECASE)}
        is_plby = ('plby' in title.lower() or 'plby' in branch.lower())
        for jid in jids:
            d = pr_data.setdefault(jid, {'open': [], 'merged': [], 'closed': [], 'plby': False})
            if state == 'OPEN':
                d['open'].append(num)
            elif state == 'MERGED':
                d['merged'].append(num)
            elif state == 'CLOSED':
                d['closed'].append(num)
            if is_plby:
                d['plby'] = True

    # Ingest candidate input
    candidate_items = []

    def ingest_text(text):
        found = re.findall(r'JSP-(\d+)', text, re.IGNORECASE)
        seen = set()
        for m in found:
            jid = f"JSP-{int(m):06d}"
            if jid not in seen:
                seen.add(jid)
                candidate_items.append((jid, jsp_catalog.get(jid, {})))

    def ingest_json_data(data):
        if isinstance(data, list):
            for item in data:
                if isinstance(item, dict) and "id" in item:
                    candidate_items.append((item["id"], item))
                elif isinstance(item, str):
                    ingest_text(item)
        elif isinstance(data, dict):
            if "entries" in data:
                for jid, meta in data["entries"].items():
                    candidate_items.append((jid, meta))
            else:
                for k, v in data.items():
                    if k.upper().startswith("JSP-"):
                        candidate_items.append((k.upper(), v if isinstance(v, dict) else {}))
                    else:
                        ingest_text(str(k))

    # Check stdin first if piped
    if not sys.stdin.isatty():
        content = sys.stdin.read().strip()
        if content:
            try:
                parsed = json.loads(content)
                ingest_json_data(parsed)
            except Exception:
                ingest_text(content)

    # Positional args if provided
    if args.candidates:
        for arg in args.candidates:
            if os.path.isfile(arg):
                try:
                    content = open(arg, encoding='utf-8', errors='replace').read()
                    try:
                        parsed = json.loads(content)
                        ingest_json_data(parsed)
                    except Exception:
                        ingest_text(content)
                except Exception as e:
                    print(f"Warning: could not read {arg}: {e}", file=sys.stderr)
            else:
                try:
                    parsed = json.loads(arg)
                    ingest_json_data(parsed)
                except Exception:
                    ingest_text(arg)

    # If no inputs from stdin or positional arguments, scan default catalog snapshot
    if not candidate_items:
        for jid in sorted(jsp_catalog.keys()):
            candidate_items.append((jid, jsp_catalog[jid]))

    # Deduplicate preserving order
    seen_candidates = set()
    unique_candidates = []
    for jid, meta in candidate_items:
        if jid not in seen_candidates:
            seen_candidates.add(jid)
            unique_candidates.append((jid, meta or jsp_catalog.get(jid, {})))

    # Filtering
    filtered_plby = 0
    filtered_open_prs = 0
    filtered_merged_prs = 0
    filtered_catalog_lean = 0
    filtered_status = 0
    filtered_closed_prs = 0

    surviving = []
    rejected = []

    for jid, meta in unique_candidates:
        title = meta.get('title', '')
        status = meta.get('status', 'Unknown')
        clean_status = re.split(r'<br>|\s', status, maxsplit=1)[0] if status else "Unknown"
        lean = meta.get('lean', '')
        eligible = meta.get('eligible', '')

        if args.status != "all":
            if args.status == "solved" and clean_status.lower() != "solved":
                filtered_status += 1
                continue
            elif args.status == "open" and clean_status.lower() != "open":
                filtered_status += 1
                continue

        reasons = []

        # 1. Catalog Lean proof
        if lean.lower() in ('yes', 'partial'):
            reasons.append(f"Catalog Lean proof: {lean}")
            filtered_catalog_lean += 1

        # 2. plby/lean-proofs
        pr_info = pr_data.get(jid, {'open': [], 'merged': [], 'closed': [], 'plby': False})
        erdos_nums = jsp_to_erdos.get(jid, set())
        solved_in_plby = sorted([e for e in erdos_nums if e in plby_erdos])

        if pr_info['plby']:
            reasons.append("plby/lean-proofs (referenced in awards PR)")
            filtered_plby += 1
        elif solved_in_plby:
            reasons.append(f"plby/lean-proofs (Erdős #{', #'.join(map(str, solved_in_plby))})")
            filtered_plby += 1

        # 3. Open awards PRs
        if pr_info['open']:
            reasons.append(f"{len(pr_info['open'])} open awards PR(s) (#{', #'.join(map(str, sorted(pr_info['open'])[:3]))}{'...' if len(pr_info['open']) > 3 else ''})")
            filtered_open_prs += 1

        # 4. Merged awards PRs
        if pr_info['merged']:
            reasons.append(f"{len(pr_info['merged'])} merged awards PR(s) (#{', #'.join(map(str, sorted(pr_info['merged'])))})")
            filtered_merged_prs += 1

        # 5. Closed awards PRs (strict mode)
        if args.strict and pr_info['closed']:
            reasons.append(f"{len(pr_info['closed'])} closed awards PR(s)")
            filtered_closed_prs += 1

        res = {
            "id": jid,
            "title": title,
            "status": clean_status,
            "eligible": eligible,
            "erdos_numbers": sorted(list(erdos_nums)),
            "open_prs": sorted(pr_info['open']),
            "merged_prs": sorted(pr_info['merged']),
            "closed_prs": sorted(pr_info['closed']),
            "reasons": reasons
        }

        if reasons:
            rejected.append(res)
        else:
            surviving.append(res)

    # JSON output format
    if args.json:
        print(json.dumps(surviving, indent=2))
        return

    # IDs only output format
    if args.ids_only:
        for s in surviving:
            print(s["id"])
        return

    # Standard / Markdown format
    prs_total = awards_doc.get('total_prs', len(prs))
    plby_total = len(plby_erdos)

    print("=" * 80)
    print(f"BOUNTY FAST FILTER — Pre-screening Report")
    print(f"Database: {prs_total} awards PRs indexed · {plby_total} plby/lean-proofs Erdős solutions")
    print(f"Filter mode: status={args.status} | strict_zero_closed_prs={'ON' if args.strict else 'OFF'}")
    print("=" * 80)
    print(f"Candidates scanned:            {len(unique_candidates)}")
    if filtered_status > 0:
        print(f"Skipped by status ({args.status}):       {filtered_status}")
    print(f"Filtered by open/merged PRs:   {filtered_open_prs + filtered_merged_prs}")
    print(f"Filtered by plby/lean-proofs:  {filtered_plby}")
    if filtered_catalog_lean > 0:
        print(f"Filtered by catalog Lean:      {filtered_catalog_lean}")
    if args.strict and filtered_closed_prs > 0:
        print(f"Filtered by closed PRs:        {filtered_closed_prs}")
    print(f"GENUINELY UNCONTESTED SHORTLIST: {len(surviving)}")
    print("-" * 80)

    if args.verbose and rejected:
        print("\nREJECTED CANDIDATES (Reason breakdown):")
        for r in rejected:
            erdos_str = f" [Erdős #{', #'.join(map(str, r['erdos_numbers']))}]" if r['erdos_numbers'] else ""
            print(f"  ❌ {r['id']}{erdos_str}: {'; '.join(r['reasons'])}")
        print("-" * 80)

    if args.markdown:
        print("\n### Surviving Uncontested Candidates\n")
        print("| JSP ID | Erdős # | Status | Eligible | Closed PRs | Title |")
        print("|---|---|---|---|---|---|")
        for s in surviving:
            e_str = ', '.join(map(str, s['erdos_numbers'])) if s['erdos_numbers'] else "—"
            closed_str = f"{len(s['closed_prs'])} (closed)" if s['closed_prs'] else "0"
            print(f"| {s['id']} | {e_str} | {s['status']} | {s['eligible'] or '—'} | {closed_str} | {s['title']} |")
    else:
        if surviving:
            print(f"\n{'JSP ID':<12} {'Erdős #':<10} {'Status':<8} {'Eligible':<16} {'PR History':<12} {'Title'}")
            print(f"{'-'*12} {'-'*10} {'-'*8} {'-'*16} {'-'*12} {'-'*30}")
            for s in surviving:
                e_str = f"#{', #'.join(map(str, s['erdos_numbers']))}" if s['erdos_numbers'] else "—"
                pr_hist = f"{len(s['closed_prs'])} closed" if s['closed_prs'] else "0 PRs"
                title_trunc = (s['title'][:45] + '...') if len(s['title']) > 45 else s['title']
                print(f"{s['id']:<12} {e_str:<10} {s['status']:<8} {(s['eligible'] or '—'):<16} {pr_hist:<12} {title_trunc}")
        else:
            print("\nNo problems survived the filter. All candidates were saturated or contested.")

    print("=" * 80)

if __name__ == "__main__":
    main()
