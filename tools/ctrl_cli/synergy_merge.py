"""
Merge scout reports (markdown with trailing ```json candidate arrays) into
docs/SYNERGY_WEIGHTS.json. Idempotent: candidates are keyed by id and
replaced; domain edges proposed by candidates or by a domain_edges block
are merged by (from,to) keeping the max weight.

Usage: python3 tools/ctrl_cli/synergy_merge.py REPORT.md [REPORT.md ...] [--dry-run]
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
WEIGHTS = ROOT / "docs" / "SYNERGY_WEIGHTS.json"
FENCE = re.compile(r"```json\s*\n(.*?)\n```", re.DOTALL)
KIND_MAP = {"explore": "explore", "productionize": "productionize", "industrialize": "industrialize"}
DOMAIN_ALIASES = {
    "codegen": "codegen_certification", "certification": "codegen_certification",
    "archive_formats": "rust_systems", "rust": "rust_systems", "numerics": "codegen_certification",
    "realtime": "realtime_systems", "real_time": "realtime_systems", "tooling": "lean_tooling",
    "lean": "lean_tooling", "nonlinear": "nonlinear_safety", "safety": "nonlinear_safety",
    "robotics_vision": "robotics", "bounties": "prizes", "grants": "prizes",
}


def extract_blocks(text: str) -> list:
    out = []
    for m in FENCE.finditer(text):
        try:
            out.append(json.loads(m.group(1)))
        except json.JSONDecodeError as e:
            print(f"  ! skipping unparsable json block: {e}", file=sys.stderr)
    return out


def norm_domains(ds, known) -> list:
    res = []
    for d in ds or []:
        d2 = DOMAIN_ALIASES.get(d, d)
        if d2 in known and d2 not in res:
            res.append(d2)
    return res


def normalise(c: dict, known_domains, known_ids) -> dict:
    c = dict(c)
    c["kind"] = KIND_MAP.get(str(c.get("kind", "explore")).lower(), "explore")
    c["domains"] = norm_domains(c.get("domains"), known_domains)
    c["builds_on"] = [b for b in c.get("builds_on", []) if b in known_ids or b == "SED"]
    c["unlocks"] = [u for u in c.get("unlocks", []) if u in known_ids]
    c["effort_weeks"] = float(c.get("effort_weeks", 4))
    c["payoff"] = max(1.0, min(5.0, float(c.get("payoff", 3))))
    c["confidence"] = max(0.0, min(1.0, float(c.get("confidence", 0.5))))
    c["status"] = "candidate"
    return c


def main(argv) -> int:
    dry = "--dry-run" in argv
    files = [Path(a) for a in argv if not a.startswith("--")]
    w = json.loads(WEIGHTS.read_text())
    index = json.loads((ROOT / "docs" / "AGENT_IDEA_INDEX.json").read_text())
    known_domains = set(w["domains"])
    existing = {c["id"]: c for c in w.get("candidates", [])}
    known_ids = {i["id"] for i in index["ideas"]} | set(existing)
    # first pass: collect all candidate ids so cross-references between lanes resolve
    staged = []
    for f in files:
        for block in extract_blocks(f.read_text()):
            if isinstance(block, list):
                staged.extend((f.name, c) for c in block if isinstance(c, dict) and "id" in c)
            elif isinstance(block, dict):
                if isinstance(block.get("candidates"), list):
                    staged.extend((f.name, c) for c in block["candidates"] if "id" in c)
                for de in block.get("domain_edges", []) or []:
                    # a dedicated domain_edges block is authoritative: replace weights
                    _merge_domain_edge(w, de, known_domains, replace=True)
                if block.get("scoring") and isinstance(block["scoring"], dict):
                    w.setdefault("scoring_proposals", []).append({"source": f.name, **block["scoring"]})
    known_ids |= {c["id"] for _, c in staged}
    added = replaced = 0
    for src, c in staged:
        n = normalise(c, known_domains, known_ids)
        n["source_report"] = src
        if n["id"] in existing:
            replaced += 1
        else:
            added += 1
        existing[n["id"]] = n
        xe = c.get("cross_domain_edge")
        if isinstance(xe, dict) and xe.get("from") and xe.get("to"):
            _merge_domain_edge(w, {**xe, "evidence": [f"candidate {n['id']}"]}, known_domains)
    order = ["IND", "ROB", "EST", "MATH", "TOOL", "SED", "XD"]
    w["candidates"] = sorted(existing.values(), key=lambda c: (
        order.index(c["id"].split("-")[0]) if c["id"].split("-")[0] in order else 99, c["id"]))
    print(f"candidates: +{added} added, {replaced} replaced, {len(w['candidates'])} total; "
          f"{len(w['domain_edges'])} domain edges")
    if not dry:
        WEIGHTS.write_text(json.dumps(w, indent=2, ensure_ascii=False) + "\n")
    return 0


def _merge_domain_edge(w: dict, de: dict, known_domains, replace: bool = False) -> None:
    a = DOMAIN_ALIASES.get(de.get("from"), de.get("from"))
    b = DOMAIN_ALIASES.get(de.get("to"), de.get("to"))
    if a not in known_domains or b not in known_domains or a == b:
        return
    try:
        wt = max(0.0, min(1.0, float(de.get("weight", 0))))
    except (TypeError, ValueError):
        return
    if wt <= 0:
        return
    for cur in w["domain_edges"]:
        if cur["from"] == a and cur["to"] == b:
            if replace or wt > cur["weight"]:
                cur["weight"] = wt
                cur["why"] = de.get("why", cur.get("why", "")) or cur.get("why", "")
            cur.setdefault("evidence", [])
            for ev in de.get("evidence", []) or []:
                if ev not in cur["evidence"]:
                    cur["evidence"].append(ev)
            return
    w["domain_edges"].append({"from": a, "to": b, "weight": wt, "why": de.get("why", ""),
                              "evidence": list(de.get("evidence", []) or [])})


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
