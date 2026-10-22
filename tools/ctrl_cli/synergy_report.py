"""
Render docs/RESEARCH_FRONTIER_<date>.md from docs/SYNERGY_WEIGHTS.json.

Usage: python3 tools/ctrl_cli/synergy_report.py [--out docs/RESEARCH_FRONTIER_2026-10.md]
The narrative header is read from docs/_frontier_preamble.md if present.
"""
from __future__ import annotations

import sys
from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))

from ctrl_cli.synergy import load_graph, pull_tier  # noqa: E402

LANES = {
    "IND": "Industrialization of verified control kernels",
    "ROB": "Robotics and vision frontier",
    "EST": "Estimation, probabilistic and learning-based control",
    "MATH": "Math prizes, bounties and open problems",
    "TOOL": "Lean ecosystem tooling and productization",
    "SED": "sediment and local-first Rust systems",
    "XD": "Cross-domain edges (projects that live on a missing edge)",
}


def md_escape(s: str) -> str:
    return (s or "").replace("|", "\\|").replace("\n", " ").strip()


def main(argv) -> int:
    out = ROOT / "docs" / f"RESEARCH_FRONTIER_{date.today():%Y-%m}.md"
    if "--out" in argv:
        out = Path(argv[argv.index("--out") + 1])
    g = load_graph(ROOT)
    w = g.weights
    cands = w.get("candidates", [])
    ranked = {r["id"]: r for r in g.rank(kinds=("candidate",))}
    lines = []
    pre = ROOT / "docs" / "_frontier_preamble.md"
    if pre.exists():
        lines.append(pre.read_text().rstrip())
    else:
        lines.append(f"# Research Frontier {date.today():%Y-%m}\n")
    lines.append("")
    lines.append("## How to read this\n")
    lines.append(
        "Every candidate below is a node in `docs/SYNERGY_WEIGHTS.json` and is scored by `./ctrl synergy rank -c`. "
        "`kind` is explore (new theorem or formalization), productionize (turn a verified result into a tested kernel or tool) "
        "or industrialize (package for a standard, customer, prize or market). `in` is the unlock in-weight from READY ideas; "
        "`wk` is honest engineer-weeks for one strong person; `conf` is the scout's confidence the opportunity is real and open. "
        "Evidence URLs were seen by the scouts in search results or fetched pages; several sandboxes could not fetch arXiv, so treat "
        "paper-level claims as pointers to verify, not citations.\n"
    )
    # Summary table, ranked
    lines.append("## Ranked shortlist\n")
    lines.append("| rank | id | kind | score | wk | conf | payoff | pull | title |")
    lines.append("| ---: | --- | --- | ---: | ---: | ---: | ---: | ---: | --- |")
    for i, r in enumerate(g.rank(kinds=("candidate",)), 1):
        c = g.nodes[r["id"]].raw
        lines.append(
            f"| {i} | `{r['id']}` | {c.get('kind')} | {r['score']:.3f} | {c.get('effort_weeks'):.0f} | "
            f"{c.get('confidence'):.2f} | {c.get('payoff'):.0f} | {pull_tier(c.get('external_pull','')):.1f} | {md_escape(c.get('title'))} |"
        )
    lines.append("")
    # Plans
    for budget in (12, 26):
        plan = g.next_plan(budget)
        lines.append(f"## Greedy plan within {budget} engineer-weeks\n")
        for r in plan:
            lines.append(f"- `{r['id']}` ({r['effort_weeks']:.0f} wk, score {r['score']:.3f}) {md_escape(r['title'])}")
        lines.append("")
    # Gaps
    lines.append("## Strong domain edges with the fewest concrete projects\n")
    lines.append("| from | to | weight | projects on edge | why |")
    lines.append("| --- | --- | ---: | ---: | --- |")
    for gp in g.gaps(0.5)[:15]:
        lines.append(f"| {gp['from']} | {gp['to']} | {gp['weight']:.1f} | {gp['idea_edges']} | {md_escape(gp['why'])} |")
    lines.append("")
    # Per-lane detail
    by_lane = {}
    for c in cands:
        by_lane.setdefault(c["id"].split("-")[0], []).append(c)
    for lane, title in LANES.items():
        items = by_lane.get(lane, [])
        if not items:
            continue
        lines.append(f"## Lane {lane}: {title}\n")
        for c in sorted(items, key=lambda c: -ranked.get(c["id"], {}).get("score", 0)):
            r = ranked.get(c["id"], {})
            lines.append(f"### `{c['id']}` {md_escape(c['title'])}\n")
            lines.append(
                f"**{c.get('kind')}** · score {r.get('score', 0):.3f} · {c.get('effort_weeks'):.0f} wk · confidence {c.get('confidence'):.2f} · "
                f"payoff {c.get('payoff'):.0f}/5 · domains: {', '.join(c.get('domains', []))}  "
            )
            if c.get("builds_on"):
                lines.append(f"Builds on: {', '.join('`'+b+'`' for b in c['builds_on'])}.  ")
            if c.get("unlocks"):
                lines.append(f"Unlocks: {', '.join('`'+u+'`' for u in c['unlocks'])}.  ")
            lines.append("")
            for key, label in (("why_now", "Why now"), ("prior_art", "Prior art"),
                               ("missing_capability", "What we would build"), ("external_pull", "External pull")):
                if c.get(key):
                    lines.append(f"- **{label}.** {md_escape(c[key])}")
            xe = c.get("cross_domain_edge")
            if isinstance(xe, dict) and xe.get("from"):
                lines.append(f"- **Edge.** {xe.get('from')} → {xe.get('to')} ({xe.get('weight')}): {md_escape(xe.get('why', ''))}")
            ev = [e for e in c.get("evidence", []) if isinstance(e, str) and e.startswith("http")]
            if ev:
                lines.append("- **Evidence.** " + " · ".join(f"<{e}>" for e in ev[:8]))
            lines.append("")
    # Domain edge appendix
    lines.append("## Appendix: domain unlock edges\n")
    lines.append("| from | to | weight | why |")
    lines.append("| --- | --- | ---: | --- |")
    for de in sorted(w["domain_edges"], key=lambda d: (-d["weight"], d["from"], d["to"])):
        lines.append(f"| {de['from']} | {de['to']} | {de['weight']:.1f} | {md_escape(de.get('why',''))} |")
    lines.append("")
    out.write_text("\n".join(lines) + "\n")
    print(f"wrote {out} ({len(cands)} candidates)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
