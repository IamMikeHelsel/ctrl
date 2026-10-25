"""Build static literature matrix and curate this campaign's public artifact set.

Run with uv run --no-sync python tools/research/build_research_site.py.
Does not deploy, approve a challenge, or copy private campaign/account metadata.
"""

import hashlib
import html
import json
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DOCS = ROOT / "docs/research/2026-10"
SITE = ROOT / "site"
ASSETS = SITE / "assets/research"


def esc(value):
    return html.escape(str(value), quote=True)


def bullets(values):
    return "<ul>" + "".join(f"<li>{esc(value)}</li>" for value in values) + "</ul>"


def build():
    records = []
    for filename, key in [("control-safety.json", "records"), ("perception-data.json", "papers")]:
        lane = json.loads((DOCS / filename).read_text())
        records.extend(lane[key])
    ids = [r["id"] for r in records]
    assert len(ids) == len(set(ids)), "Source ids must be unique"
    for r in records:
        assert "2026-08-21" <= r["publication_date"] <= "2026-10-21", r["id"]
        assert r["url"].startswith("https://arxiv.org/"), r["id"]
    data = {
        "schema_version": 1,
        "as_of": "2026-10-21",
        "window": {"from": "2026-08-21", "to": "2026-10-21"},
        "coverage": "Targeted survey, not systematic or exhaustive; all dates are first preprint submissions.",
        "disclosure": "AI-assisted primary-source triage; no independent human review or source-paper reproduction claimed.",
        "confidence_meaning": "Subjective confidence in scoping/priority, not calibrated probability of correctness or discovery.",
        "records": records,
    }
    (SITE / "research.json").write_text(json.dumps(data, indent=2) + "\n")
    markdown = [
        "# Mathematics × physics research matrix — 21 October 2026",
        "",
        "17 targeted primary-source cards; 21 August–21 October 2026 preprint window.",
        "Dates are first submissions, not peer-review or acceptance dates. Relevant passages",
        "were inspected; no source paper was independently reproduced. Proposals are our",
        "candidate transfers, not claims made by the papers. See lane JSON for full provenance.",
        "",
        "| Source / preprint date | Mathematics | Physical model / measurement | Candidate transfer |",
        "| --- | --- | --- | --- |",
    ]
    rows, details = [], []
    for r in records:
        claim = r["theorem_or_claim"]
        math = "; ".join(r["mathematical_domains"])
        physics = "; ".join(r["physical_domains"])
        search = " ".join([r["id"], r["title"], math, physics, *r["application_domains"]])
        markdown.append(
            f"| [{r['id']} · {r['title']}]({r['url']}) · {r['publication_date']} "
            f"| {math} | {physics} | {r['proposed_new_question']} |"
        )
        rows.append(f"""<tr data-search="{esc(search.lower())}">
<th scope="row"><a href="{esc(r["url"])}">{esc(r["title"])}</a>
<p class="small muted">{esc(r["id"])} · {esc(r["publication_date"])} · preprint</p>
<a href="#{esc(r["id"])}" class="small">Assumptions and proposed test ↓</a></th>
<td><strong>{esc(math)}</strong><p class="muted">× {esc(physics)}</p></td>
<td>{esc(r["proposed_new_question"])}<p class="small muted">{esc(", ".join(r["application_domains"]))}</p></td></tr>""")
        read = r["source_read"]
        read_scope = (
            read
            if isinstance(read, str)
            else ("; ".join(read.get("locations", [])) + ". " + read.get("limit", ""))
        )
        full_url = r.get("full_text_url") or (
            read.get("url") if isinstance(read, dict) else r["url"]
        )
        details.append(f"""<details id="{esc(r["id"])}" data-search="{esc(search.lower())}">
<summary>{esc(r["id"])} · {esc(r["title"])}</summary>
<p class="small muted">{esc(", ".join(r["authors"]))} · {esc(r["publication_date"])} · <a href="{esc(full_url)}">Inspected source</a></p>
<p><strong>Source claim ({esc(claim["location"])}):</strong> {esc(claim["summary"])}</p>
<p class="small muted">Read scope: {esc(read_scope)}</p>
<div class="grid"><div><h3>Assumptions</h3>{bullets(r["assumptions"])}
<h3>Failure modes</h3>{bullets(r["failure_modes"])}</div>
<div><h3>Proposed ctrl experiment</h3><p>{esc(r["prototype"])}</p>
<p><strong>Baseline:</strong> {esc(r["baseline"])}</p>
<p><strong>Measure:</strong> {esc("; ".join(r["metrics"]))}</p>
<p><strong>Falsifier:</strong> {esc(r["falsifier"])}</p></div></div>
<p class="small muted">{esc(r["novelty_status"])} Scoping confidence: {r["confidence"]["percent"]}% (subjective, uncalibrated). {esc(r["confidence"]["rationale"])}</p>
</details>""")
    (DOCS / "MATRIX.md").write_text("\n".join(markdown) + "\n")
    document = """<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Research matrix · ctrl</title><meta name="description" content="A sourced mathematics and physics research matrix for robotics: assumptions, experiments and falsifiers.">
<link rel="icon" href="favicon.svg" type="image/svg+xml"><link rel="stylesheet" href="style.css"><link rel="stylesheet" href="research.css"><script src="research.js" defer></script></head>
<body><a class="skip-link" href="#main">Skip to content</a><div class="page"><header>
<div class="breadcrumbs"><a href="index.html">ctrl</a> / Research matrix</div>
<div class="eyebrow">Literature → questions → small experiments</div><h1>Useful connections.<br>Visible assumptions.</h1>
<p class="subtitle">A targeted survey of 17 preprints from 21 August–21 October 2026. Each pairs a mathematical tool with a physical model and an experiment that could fail.</p>
<nav class="nav-links" aria-label="Research navigation"><a href="#matrix">Matrix</a><a href="#sources">Source cards</a><a href="#plan">Plan</a><a href="studies/latency-braking.html">Braking study</a><a href="studies/transport.html">Transport study</a><a href="research.json">Download source data</a></nav>
</header><main id="main"><section><h2>Start where the bridge is small</h2><div class="grid">
<article class="panel"><span class="label">01 · prototype</span><h3><a href="studies/latency-braking.html">State age × braking dynamics</a></h3><p>Carry uncertainty and reaction time into a stopping envelope. Test false admissions, then validate the supplied bounds.</p></article>
<article class="panel"><span class="label">02 · prototype</span><h3><a href="studies/transport.html">Duality × mass-conserving allocation</a></h3><p>Check an assignment's feasibility and cost gap from a small exact witness. Keep the allocation claim separate from collision avoidance.</p></article>
<article class="panel"><span class="label">03 · proposed</span><h3>Exact certificates for pose estimates</h3><p>Try rational or interval replay of a numerical optimality certificate. Measure rejection, gap and checking cost before scaling to geometry.</p></article></div>
<aside class="note">These papers seed questions; they do not validate ctrl. Dates are first preprint submissions. We inspected relevant full-text passages, not every proof or implementation. This is neither an exhaustive review nor a claim of new mathematics.</aside></section>
<section id="matrix"><h2>Mathematics × physical model</h2>
<div class="filter"><label for="search">Filter by topic, source or domain</label><input id="search" type="search" placeholder="e.g. latency, transport, perception" aria-controls="matrix-table source-cards"><p id="result-count" role="status">17 source records</p></div>
<div class="table-wrap" role="region" aria-label="Research matrix, horizontally scrollable" tabindex="0"><table id="matrix-table">
<caption>Proposed transfers are our research questions; they are not findings established by these papers.</caption>
<thead><tr><th scope="col">Source</th><th scope="col">Mathematics × physics</th><th scope="col">Proposed transfer</th></tr></thead><tbody>ROWS</tbody></table></div></section>
<section id="sources"><h2>Source cards and conditions</h2><p class="muted">Expand a card for the assumptions, baseline and falsifier. Confidence is a subjective assessment of research fit, not a probability of a correct theorem or a discovery.</p><div id="source-cards">DETAILS</div></section>
<section id="plan"><h2>A small, gated research program</h2><ol class="research-steps">
<li><strong>Read the actual result.</strong> Freeze source version, claim location, assumptions and inspected scope. An abstract can suggest a lead.</li>
<li><strong>Identify the missing bridge.</strong> Connect mathematical object, physical model, available measurements and executable check.</li>
<li><strong>Build a falsifiable slice.</strong> Specify a fair baseline, units, admissible cases and failure conditions before measuring.</li>
<li><strong>Have another reviewer try to break it.</strong> Include boundary conditions, malformed witnesses, stale state and mismatched assumptions.</li>
<li><strong>Publish the bounded conclusion.</strong> Save replay commands and results. Write-ups and animations explain only what the evidence supports.</li></ol>
<p class="measure">Next priorities: integrate bounded state age without double-counting delay; test transport certificates against independent assignment optima; investigate pose-certificate reconstruction. Broader closed-loop, sensor and hardware studies follow only if those slices hold up.</p>
<p class="measure">A release requires an exact reviewed revision, passing checks, source and licensing review, and consistent claims across code, documentation and site. Public repository availability is a separate decision.</p></section>
</main><footer><span>AI-assisted research and writing · 21 October 2026</span><a href="index.html">Back to ctrl</a></footer></div></body></html>"""
    (SITE / "research.html").write_text(
        document.replace("ROWS", "".join(rows)).replace("DETAILS", "".join(details))
    )
    ASSETS.mkdir(parents=True, exist_ok=True)
    public_files = [
        "LICENSE",
        "experiments/research/latency_braking.py",
        "experiments/research/latency_braking_scene.py",
        "lean/Research/LatencyBraking.lean",
        "tests/test_latency_braking.py",
        "work/research/2026-10/latency-braking-results.json",
    ]
    optional = [
        "experiments/research/transport_certificate.py",
        "tests/test_transport_certificate.py",
        "work/research/2026-10/transport-results.json",
        "lean/Research/TransportCertificate.lean",
    ]
    public_files.extend(path for path in optional if (ROOT / path).is_file())
    artifacts = []
    for relative in public_files:
        src = ROOT / relative
        shutil.copyfile(src, ASSETS / src.name)
        artifacts.append(
            {
                "source": relative,
                "file": src.name,
                "sha256": hashlib.sha256(src.read_bytes()).hexdigest(),
            }
        )
    (ASSETS / "manifest.json").write_text(
        json.dumps(
            {
                "as_of": "2026-10-21",
                "scope": "Curated local research snapshots; no deployment or source-refinement proof implied.",
                "artifacts": artifacts,
            },
            indent=2,
        )
        + "\n"
    )
    print(f"Built {len(records)} source rows and {len(artifacts)} curated artifact snapshots")


if __name__ == "__main__":
    build()
