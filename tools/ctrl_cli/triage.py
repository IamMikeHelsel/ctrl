"""
Triage module for rapid bounty screening.
Cross-references candidate problems against TheJustinSunPrize/awards PRs and plby/lean-proofs.
"""

import sys
import os
import json
import re
from pathlib import Path


def run_bounty_filter(args, repo_root, data_dir):
    awards_path = data_dir / "awards_prs.json"
    plby_path = data_dir / "plby_erdos.json"
    map_path = data_dir / "jsp_erdos_map.json"
    jsp_path = data_dir / "jsp.json"

    # Fallback to ctrl-claude if local data missing
    if not awards_path.exists():
        data_dir = repo_root.parent / "ctrl-claude" / "data" / "snapshots"
        awards_path = data_dir / "awards_prs.json"
        plby_path = data_dir / "plby_erdos.json"
        map_path = data_dir / "jsp_erdos_map.json"
        jsp_path = data_dir / "jsp.json"

    awards_doc = json.loads(awards_path.read_text()) if awards_path.exists() else {}
    plby_doc = json.loads(plby_path.read_text()) if plby_path.exists() else {}
    map_doc = json.loads(map_path.read_text()) if map_path.exists() else {}
    jsp_catalog = (
        json.loads(jsp_path.read_text()).get("entries", {}) if jsp_path.exists() else {}
    )

    plby_erdos = set(plby_doc.get("solved_erdos", []))
    jsp_to_erdos = {k: set(v) for k, v in map_doc.get("mappings", {}).items()}

    # Index awards PRs
    prs = awards_doc.get("prs", [])
    pr_data = {}

    for pr in prs:
        num = pr["number"]
        title = pr.get("title", "")
        branch = pr.get("head", "")
        state = pr.get("state", "").upper()
        jids = {
            f"JSP-{int(j):06d}"
            for j in re.findall(r"JSP-(\d+)", title, re.IGNORECASE)
            + re.findall(r"jsp-(\d+)", branch, re.IGNORECASE)
        }
        is_plby = "plby" in title.lower() or "plby" in branch.lower()
        for jid in jids:
            if jid not in pr_data:
                pr_data[jid] = {"open": [], "merged": [], "closed": [], "plby": False}
            if is_plby:
                pr_data[jid]["plby"] = True
            if state == "OPEN":
                pr_data[jid]["open"].append(num)
            elif state == "MERGED":
                pr_data[jid]["merged"].append(num)
            else:
                pr_data[jid]["closed"].append(num)

    # Determine input candidates
    candidates = []
    if args.candidates:
        for c in args.candidates:
            if os.path.exists(c):
                content = Path(c).read_text()
                if c.endswith(".json"):
                    try:
                        data = json.loads(content)
                        if isinstance(data, list):
                            candidates.extend(data)
                        elif isinstance(data, dict):
                            candidates.extend(data.values())
                    except Exception:
                        pass
                else:
                    found = re.findall(r"JSP-\d{6}", content)
                    for fid in set(found):
                        candidates.append({"id": fid})
            elif re.match(r"^JSP-\d+$", c, re.IGNORECASE):
                num = int(re.sub(r"[^\d]", "", c))
                candidates.append({"id": f"JSP-{num:06d}"})
    elif not sys.stdin.isatty():
        stdin_content = sys.stdin.read()
        found = re.findall(r"JSP-\d{6}", stdin_content)
        for fid in set(found):
            candidates.append({"id": fid})
    else:
        candidates = list(jsp_catalog.values())

    survivors = []
    rejected = []

    for item in candidates:
        if isinstance(item, dict):
            jid = item.get("id") or item.get("problem_id")
            title = item.get("title", "")
            cat_status = item.get("status", "")
            has_lean_proof = item.get("has_lean_proof", False)
        elif isinstance(item, str):
            jid = item
            title = ""
            cat_status = ""
            has_lean_proof = False
        else:
            continue

        if not jid:
            continue

        cat_entry = jsp_catalog.get(jid, {})
        if not title:
            title = cat_entry.get("title", "")
        if not cat_status:
            cat_status = cat_entry.get("status", "")
        if not has_lean_proof:
            has_lean_proof = cat_entry.get("has_lean_proof", False)

        if args.status != "all" and cat_status:
            if cat_status.lower() != args.status.lower():
                continue

        # Check rejection criteria
        reasons = []

        # 1. Awards PRs
        pinfo = pr_data.get(jid)
        if pinfo:
            if pinfo["open"]:
                reasons.append(
                    f"{len(pinfo['open'])} open awards PR(s) ({', '.join(f'#{n}' for n in pinfo['open'][:3])})"
                )
            if pinfo["merged"]:
                reasons.append(f"{len(pinfo['merged'])} merged awards PR(s)")
            if (
                args.strict
                and pinfo["closed"]
                and not (pinfo["open"] or pinfo["merged"])
            ):
                reasons.append(
                    f"{len(pinfo['closed'])} closed awards PR(s) (strict zero-competition)"
                )

        # 2. plby/lean-proofs
        erdos_ids = jsp_to_erdos.get(jid, set())
        erdos_in_plby = erdos_ids.intersection(plby_erdos)
        if erdos_in_plby:
            reasons.append(
                f"in plby/lean-proofs (Erdős {', '.join(str(e) for e in sorted(erdos_in_plby))})"
            )
        elif pinfo and pinfo.get("plby"):
            reasons.append("has plby claim in awards PRs")

        # 3. Catalog says Lean proof exists
        if has_lean_proof:
            reasons.append("JSP catalog marked 'Lean proof: Yes'")

        if reasons:
            rejected.append((jid, title, "; ".join(reasons)))
        else:
            survivors.append((jid, title, cat_status))

    # Output formatting
    if args.ids_only:
        for jid, _, _ in survivors:
            print(jid)
        return

    if args.json:
        out = [
            {"id": jid, "title": title, "status": status}
            for jid, title, status in survivors
        ]
        print(json.dumps(out, indent=2))
        return

    print("\n\033[1m\033[36m=== Bounty Fast-Filter Results ===\033[0m")
    print(f"Scanned candidates:   \033[1m{len(candidates)}\033[0m")
    print(f"Rejected (contested): \033[31m{len(rejected)}\033[0m")
    print(f"Surviving shortlist:  \033[32m\033[1m{len(survivors)}\033[0m\n")

    if args.verbose and rejected:
        print("\033[1m\033[33mSample Rejections:\033[0m")
        for jid, title, reason in rejected[:10]:
            print(f"  \033[31m✖\033[0m \033[1m{jid}\033[0m: {reason}")
        if len(rejected) > 10:
            print(f"  ... and {len(rejected) - 10} more.\n")

    if survivors:
        print("\033[1m\033[32mSurviving Uncontested Problems:\033[0m")
        for jid, title, status in survivors:
            print(f"  \033[32m✔\033[0m \033[1m{jid}\033[0m [{status}]: {title}")
    else:
        print(
            "\033[33mNo candidate survived filters. All candidates are contested, solved, or have active PRs.\033[0m"
        )
    print()
