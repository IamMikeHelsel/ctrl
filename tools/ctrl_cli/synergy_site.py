"""
Render site/synergy.html (static, self-contained) from docs/SYNERGY_WEIGHTS.json:
a domain-by-domain unlock heatmap, the ranked candidate table with lane and
kind filters, and per-candidate detail. No external assets.

Usage: python3 tools/ctrl_cli/synergy_site.py
"""
from __future__ import annotations

import html
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))

from ctrl_cli.synergy import load_graph, pull_tier  # noqa: E402

CSS = """
:root{--bg:#0f1115;--fg:#e6e6e6;--mute:#9aa0a6;--line:#262a33;--card:#161a21;--acc:#6ea8fe;
--k0:#1b2230;--k1:#1d3a5c;--k2:#1f5a8a;--k3:#2a7fbf;--k4:#53a8e6;}
@media (prefers-color-scheme: light){:root{--bg:#fbfbfc;--fg:#1b1f24;--mute:#5c6570;--line:#e3e6ea;--card:#fff;--acc:#1f5a8a;
--k0:#eef2f7;--k1:#cfe0f3;--k2:#9cc3e8;--k3:#5b9fd6;--k4:#2a7fbf;}}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--fg);font:15px/1.5 -apple-system,Segoe UI,Inter,sans-serif}
.page{max-width:1180px;margin:0 auto;padding:1.5rem 16px 4rem}h1{font-size:1.6rem;margin:.2rem 0}h2{font-size:1.15rem;margin:2rem 0 .6rem}
.sub{color:var(--mute)}a{color:var(--acc)}code{font-family:ui-monospace,SFMono-Regular,Menlo,monospace;font-size:.9em}
table{border-collapse:collapse;width:100%}th,td{border-bottom:1px solid var(--line);padding:.35rem .5rem;text-align:left;vertical-align:top}
th{color:var(--mute);font-weight:600;font-size:.8rem;text-transform:uppercase;letter-spacing:.03em}
.heat{overflow-x:auto}.heat table{width:auto}.heat td{text-align:center;min-width:3.2rem;height:2.2rem;border:1px solid var(--bg)}
.heat th.row{text-align:right;white-space:nowrap;font-size:.75rem;text-transform:none}
.heat th.col{writing-mode:vertical-rl;transform:rotate(180deg);text-align:left;font-size:.75rem;text-transform:none;height:9rem}
.k0{background:var(--k0)}.k1{background:var(--k1)}.k2{background:var(--k2)}.k3{background:var(--k3);color:#fff}.k4{background:var(--k4);color:#fff}
.filters{display:flex;gap:.6rem;flex-wrap:wrap;margin:.6rem 0}select,input{background:var(--card);color:var(--fg);border:1px solid var(--line);border-radius:6px;padding:.35rem .5rem}
.num{text-align:right;font-variant-numeric:tabular-nums}.tag{display:inline-block;border:1px solid var(--line);border-radius:999px;padding:0 .5rem;font-size:.75rem;color:var(--mute);margin-right:.2rem}
details{background:var(--card);border:1px solid var(--line);border-radius:8px;padding:.6rem .9rem;margin:.5rem 0}summary{cursor:pointer}
.ev a{display:inline-block;margin-right:.6rem;word-break:break-all}.small{font-size:.85rem;color:var(--mute)}
"""

JS = """
const rows=[...document.querySelectorAll('tbody#cands tr')];
const lane=document.getElementById('lane'),kind=document.getElementById('kind'),q=document.getElementById('q');
function apply(){const l=lane.value,k=kind.value,s=q.value.toLowerCase();let n=0;
 for(const r of rows){const ok=(l==='all'||r.dataset.lane===l)&&(k==='all'||r.dataset.kind===k)&&(!s||r.dataset.text.includes(s));r.style.display=ok?'':'none';if(ok)n++;}
 document.getElementById('count').textContent=n;}
for(const el of [lane,kind,q]) el.addEventListener('input',apply);apply();
"""


def kclass(w: float) -> str:
    return "k0" if w <= 0 else "k1" if w < 0.35 else "k2" if w < 0.6 else "k3" if w < 0.8 else "k4"


def main() -> int:
    g = load_graph(ROOT)
    w = g.weights
    m = g.matrix()
    keys = m["domains"]
    labels = {k: w["domains"][k]["label"] for k in keys}
    e = html.escape
    out = []
    out.append(f"<!doctype html><html lang='en'><head><meta charset='utf-8'><meta name='viewport' content='width=device-width,initial-scale=1'>")
    out.append("<title>ctrl Synergy Lens</title><style>" + CSS + "</style></head><body><div class='page'>")
    out.append("<h1>ctrl Synergy Lens</h1><p class='sub'>Which domains unlock which, and what to pick up next. Generated from "
               "<a href='SYNERGY_WEIGHTS.json'>SYNERGY_WEIGHTS.json</a> and <a href='AGENT_IDEA_INDEX.json'>AGENT_IDEA_INDEX.json</a> "
               f"(updated {e(w.get('updated_at',''))}). Query locally with <code>./ctrl synergy</code>. "
               "<a href='index.html'>Back to the project site</a>.</p>")
    # Heatmap
    out.append("<h2>Domain unlock matrix</h2><p class='small'>Row unlocks column; weight 0–1. Hover a cell for the justification.</p><div class='heat'><table><thead><tr><th></th>")
    for k in keys:
        out.append(f"<th class='col'>{e(labels[k])}</th>")
    out.append("</tr></thead><tbody>")
    for a, row in zip(keys, m["rows"]):
        out.append(f"<tr><th class='row'>{e(labels[a])}</th>")
        for b, wt in zip(keys, row):
            if wt is None:
                out.append("<td class='k0'>·</td>")
            else:
                de = g.domain_edges.get((a, b), {})
                title = e(de.get("why", "")) if wt > 0 else ""
                out.append(f"<td class='{kclass(wt)}' title='{title}'>{wt:.1f}</td>" if wt > 0 else "<td class='k0'></td>")
        out.append("</tr>")
    out.append("</tbody></table></div>")
    # Gaps
    out.append("<h2>Strong edges with the fewest projects</h2><table><thead><tr><th>from</th><th>to</th><th>weight</th><th>projects</th><th>why</th></tr></thead><tbody>")
    for gp in g.gaps(0.5)[:10]:
        out.append(f"<tr><td>{e(gp['from'])}</td><td>{e(gp['to'])}</td><td class='num'>{gp['weight']:.1f}</td><td class='num'>{gp['idea_edges']}</td><td>{e(gp['why'])}</td></tr>")
    out.append("</tbody></table>")
    # Candidates
    ranked = g.rank(kinds=("candidate",))
    lanes = sorted({r["id"].split("-")[0] for r in ranked})
    out.append("<h2>Ranked candidates</h2><div class='filters'><select id='lane'><option value='all'>all lanes</option>")
    for l in lanes:
        out.append(f"<option value='{l}'>{l}</option>")
    out.append("</select><select id='kind'><option value='all'>all kinds</option><option value='explore'>explore</option>"
               "<option value='productionize'>productionize</option><option value='industrialize'>industrialize</option></select>"
               "<input id='q' placeholder='filter text…' size='28'><span class='small'><span id='count'></span> shown</span></div>")
    out.append("<table><thead><tr><th>#</th><th>id</th><th>kind</th><th>score</th><th>wk</th><th>conf</th><th>payoff</th><th>pull</th><th>title</th></tr></thead><tbody id='cands'>")
    for i, r in enumerate(ranked, 1):
        c = g.nodes[r["id"]].raw
        text = e((c.get("title", "") + " " + " ".join(c.get("domains", [])) + " " + c.get("why_now", "")).lower())
        out.append(f"<tr data-lane='{r['id'].split('-')[0]}' data-kind='{e(c.get('kind',''))}' data-text='{text}'>"
                   f"<td class='num'>{i}</td><td><a href='#{r['id']}'><code>{r['id']}</code></a></td><td>{e(c.get('kind',''))}</td>"
                   f"<td class='num'>{r['score']:.3f}</td><td class='num'>{c.get('effort_weeks',0):.0f}</td><td class='num'>{c.get('confidence',0):.2f}</td>"
                   f"<td class='num'>{c.get('payoff',0):.0f}</td><td class='num'>{pull_tier(c.get('external_pull','')):.1f}</td><td>{e(c.get('title',''))}</td></tr>")
    out.append("</tbody></table>")
    out.append("<h2>Candidate detail</h2>")
    for r in ranked:
        c = g.nodes[r["id"]].raw
        out.append(f"<details id='{r['id']}'><summary><code>{r['id']}</code> {e(c.get('title',''))} "
                   f"<span class='tag'>{e(c.get('kind',''))}</span><span class='tag'>{c.get('effort_weeks',0):.0f} wk</span>"
                   f"<span class='tag'>score {r['score']:.3f}</span></summary>")
        out.append("<p class='small'>" + " ".join(f"<span class='tag'>{e(d)}</span>" for d in c.get("domains", [])) +
                   (f" builds on {', '.join('<code>'+e(b)+'</code>' for b in c.get('builds_on', []))}" if c.get("builds_on") else "") +
                   (f" · unlocks {', '.join('<code>'+e(u)+'</code>' for u in c.get('unlocks', []))}" if c.get("unlocks") else "") + "</p>")
        for key, label in (("why_now", "Why now"), ("prior_art", "Prior art"), ("missing_capability", "What we would build"), ("external_pull", "External pull")):
            if c.get(key):
                out.append(f"<p><strong>{label}.</strong> {e(c[key])}</p>")
        ev = [x for x in c.get("evidence", []) if isinstance(x, str) and x.startswith("http")]
        if ev:
            out.append("<p class='ev small'>" + " ".join(f"<a href='{e(u)}'>{e(u[:70])}{'…' if len(u) > 70 else ''}</a>" for u in ev[:8]) + "</p>")
        out.append("</details>")
    out.append("</div><script>" + JS + "</script></body></html>")
    (ROOT / "site" / "synergy.html").write_text("\n".join(out))
    (ROOT / "site" / "SYNERGY_WEIGHTS.json").write_text(json.dumps(w, indent=2, ensure_ascii=False) + "\n")
    print("wrote site/synergy.html and site/SYNERGY_WEIGHTS.json")
    return 0


if __name__ == "__main__":
    sys.exit(main())
