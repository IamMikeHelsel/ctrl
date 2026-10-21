"""
Triage module for rapid bounty and formal-conjecture screening.
Cross-references candidate problems against TheJustinSunPrize/awards PRs,
plby/lean-proofs, and DeepMind's FormalConjectures repository across all 17 categories.
"""

import sys
import os
import json
import re
from pathlib import Path


DECL_PATTERN = re.compile(
    r"@\[([^\]]*category\s+([^\],\n]+)[^\]]*)\]\s*(?:@\[[^\]]*\]\s*)*(?:theorem|lemma)\s+([^\s({:]+)((?:(?!:=|\n@\[).)*?):=\s*(?:by\s+)?sorry\b",
    re.DOTALL,
)


def _find_formal_conjectures_root(repo_root: Path) -> Path:
    candidates = [
        Path.home() / "Dev" / "formal-conjectures" / "FormalConjectures",
        repo_root.parent / "formal-conjectures" / "FormalConjectures",
        Path.home()
        / "Dev"
        / "ctrl-erdos-lab"
        / ".lake"
        / "packages"
        / "formal_conjectures"
        / "FormalConjectures",
    ]
    for p in candidates:
        if p.exists():
            return p
    return candidates[0]


def _scan_formal_conjectures(fc_root: Path, include_erdos: bool, include_non_erdos: bool, category_filter=None):
    items = []
    if not fc_root.exists():
        return items
    for cat_dir in sorted(fc_root.iterdir()):
        if not cat_dir.is_dir() or cat_dir.name == "Util":
            continue
        is_erdos = cat_dir.name == "ErdosProblems"
        if is_erdos and not include_erdos:
            continue
        if not is_erdos and not include_non_erdos:
            continue
        if category_filter and cat_dir.name.lower() != category_filter.lower():
            continue

        for f in sorted(cat_dir.rglob("*.lean")):
            txt = f.read_text(errors="ignore")
            has_formal_proof = "formal_proof" in txt
            erdos_num = int(f.stem) if (is_erdos and f.stem.isdigit()) else None
            for m in DECL_PATTERN.finditer(txt):
                cat_raw = m.group(2).strip()
                thm_name = m.group(3).strip()
                sig = " ".join(m.group(4).strip().split())
                if len(sig) > 95:
                    sig = sig[:92] + "..."
                is_open = "open" in cat_raw.lower()
                status = "open" if is_open else "solved"
                item_id = (
                    f"ERDOS-{erdos_num:04d}:{thm_name}"
                    if erdos_num is not None
                    else f"FC-{cat_dir.name}/{f.stem}:{thm_name}"
                )
                items.append(
                    {
                        "id": item_id,
                        "title": f"[{cat_raw}] {thm_name} {sig}".strip(),
                        "status": status,
                        "category": cat_dir.name,
                        "category_tag": cat_raw,
                        "erdos_id": erdos_num,
                        "has_lean_proof": has_formal_proof,
                        "file": str(f.relative_to(fc_root.parent)),
                    }
                )
    return items


def run_bounty_filter(args, repo_root, data_dir):
    awards_path = data_dir / "awards_prs.json"
    plby_path = data_dir / "plby_erdos.json"
    map_path = data_dir / "jsp_erdos_map.json"
    jsp_path = data_dir / "jsp.json"

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
    erdos_to_jsp = {}
    for jid, eids in jsp_to_erdos.items():
        for eid in eids:
            erdos_to_jsp.setdefault(eid, set()).add(jid)

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

    source = getattr(args, "source", "jsp")
    category_filter = getattr(args, "category", None)
    limit = getattr(args, "limit", 0) or 0

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
        if source in ("jsp", "all") and not category_filter:
            candidates.extend([{"id": k, **v} for k, v in jsp_catalog.items()])
        if source in ("erdos", "fc", "all"):
            fc_root = _find_formal_conjectures_root(repo_root)
            candidates.extend(
                _scan_formal_conjectures(
                    fc_root,
                    include_erdos=(source in ("erdos", "all")),
                    include_non_erdos=(source in ("fc", "all")),
                    category_filter=category_filter,
                )
            )

    survivors = []
    rejected = []

    for item in candidates:
        if isinstance(item, dict):
            jid = item.get("id") or item.get("problem_id")
            title = item.get("title", "")
            cat_status = item.get("status", "")
            has_lean_proof = bool(
                item.get("has_lean_proof", False)
                or str(item.get("lean", "")).lower() == "yes"
            )
            explicit_erdos_id = item.get("erdos_id")
        elif isinstance(item, str):
            jid = item
            title = ""
            cat_status = ""
            has_lean_proof = False
            explicit_erdos_id = None
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
            has_lean_proof = bool(
                cat_entry.get("has_lean_proof", False)
                or str(cat_entry.get("lean", "")).lower() == "yes"
            )

        if args.status != "all" and cat_status:
            if cat_status.lower() != args.status.lower():
                continue

        # Check rejection criteria
        reasons = []

        # 1. Awards PRs (direct JSP or mapped from Erdős ID)
        related_jids = {jid} if jid.startswith("JSP-") else set()
        if explicit_erdos_id is not None:
            related_jids |= erdos_to_jsp.get(explicit_erdos_id, set())

        for rjid in sorted(related_jids):
            pinfo = pr_data.get(rjid)
            if pinfo:
                if pinfo["open"]:
                    reasons.append(
                        f"{len(pinfo['open'])} open awards PR(s) on {rjid} ({', '.join(f'#{n}' for n in pinfo['open'][:3])})"
                    )
                if pinfo["merged"]:
                    reasons.append(f"{len(pinfo['merged'])} merged awards PR(s) on {rjid}")
                if (
                    args.strict
                    and pinfo["closed"]
                    and not (pinfo["open"] or pinfo["merged"])
                ):
                    reasons.append(
                        f"{len(pinfo['closed'])} closed awards PR(s) on {rjid} (strict zero-competition)"
                    )

        # 2. plby/lean-proofs
        erdos_ids = set(jsp_to_erdos.get(jid, set()))
        if explicit_erdos_id is not None:
            erdos_ids.add(explicit_erdos_id)
        erdos_in_plby = erdos_ids.intersection(plby_erdos)
        if erdos_in_plby:
            reasons.append(
                f"in plby/lean-proofs (Erdős {', '.join(str(e) for e in sorted(erdos_in_plby))})"
            )
        else:
            for rjid in sorted(related_jids):
                pinfo = pr_data.get(rjid)
                if pinfo and pinfo.get("plby"):
                    reasons.append(f"has plby claim in awards PRs ({rjid})")

        # 3. Catalog says Lean proof exists
        if has_lean_proof:
            reasons.append("Catalog/file marked as already having formal proof")

        if reasons:
            rejected.append((jid, title, "; ".join(reasons)))
        else:
            survivors.append((jid, title, cat_status))

    shown_survivors = survivors[:limit] if limit > 0 else survivors

    # Output formatting
    if args.ids_only:
        for jid, _, _ in shown_survivors:
            print(jid)
        return

    if args.json:
        out = [
            {"id": jid, "title": title, "status": status}
            for jid, title, status in shown_survivors
        ]
        print(json.dumps(out, indent=2))
        return

    print("\n\033[1m\033[36m=== Bounty & FormalConjectures Fast-Filter Results ===\033[0m")
    print(f"Source catalog:       \033[1m{source}\033[0m" + (f" (category={category_filter})" if category_filter else ""))
    print(f"Scanned candidates:   \033[1m{len(candidates)}\033[0m")
    print(f"Rejected (contested): \033[31m{len(rejected)}\033[0m")
    print(f"Surviving shortlist:  \033[32m\033[1m{len(survivors)}\033[0m\n")

    if args.verbose and rejected:
        print("\033[1m\033[33mSample Rejections:\033[0m")
        for jid, title, reason in rejected[:10]:
            print(f"  \033[31m✖\033[0m \033[1m{jid}\033[0m: {reason}")
        if len(rejected) > 10:
            print(f"  ... and {len(rejected) - 10} more.\n")

    if shown_survivors:
        print("\033[1m\033[32mSurviving Uncontested Problems:\033[0m")
        for jid, title, status in shown_survivors:
            print(f"  \033[32m✔\033[0m \033[1m{jid}\033[0m [{status}]: {title}")
        if limit > 0 and len(survivors) > limit:
            print(f"  ... showing {limit} of {len(survivors)} surviving problems.")
    else:
        print(
            "\033[33mNo candidate survived filters. All candidates are contested, solved, or have active PRs.\033[0m"
        )
    print()
