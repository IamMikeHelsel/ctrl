# Research pass verification — 21 October 2026

## Delivered

- 17 dated primary-source cards: 9 control/safety, 8 perception/data; targeted
  theorem/method inspection, not exhaustive paper reproduction or human peer review.
- Mathematics × physical-model matrix, machine-readable source data, staged program,
  two reproducible prototype studies, and independent AI claim/arithmetic review.
- Delayed braking: exact 34,560-case factorial grid, 10 focused tests, four Lean
  declarations, sensitivity analysis, interactive explanation and 25-second Manim video.
- Finite transport: exact primal/dual checking, 18 focused tests, 912 candidate
  intervals against independent enumeration, two Lean declarations and a study page.
- Revised homepage and evidence framing, accessible search/source cards, mobile layout,
  explicit retirement of the stale public idea catalog, and a curated site snapshot.

## Commands and observed outcomes

| Check | Outcome |
| --- | --- |
| `uv run pytest -q` before additions | 255 passed, 1 deselected, 16.84 s |
| `uv run --no-sync pytest -q` after additions | 283 passed, 1 deselected, 19.09 s |
| Focused new tests | 10 braking + 18 transport pass; each focused run under 0.1 s |
| `lake env lean Research/LatencyBraking.lean` | Pass; all four printed axiom lists use only propext, Classical.choice, Quot.sound |
| `lake env lean Research/TransportCertificate.lean` | Pass; both printed axiom lists use only propext, Classical.choice, Quot.sound |
| `lake build Research` after importing both new modules | Pass; 8,735 jobs (mostly reused), aggregate Research built successfully |
| Explicit Ruff lint/format on campaign Python and tooling | Pass |
| Repository Ruff lint | Fails: 8 initial issues, 9 at final check; the additional issue is in concurrently added `site/sketches/braking_shield.py` |
| Repository Ruff format check | Fails: 20 initial files, 22 at final check; new out-of-scope guide/sketch appeared during the session |
| `uv run ctrl check --all` | Exit 3: all six solutions build, pass token/axiom/binding checks; all six are NOT_APPROVED |
| JavaScript syntax | Both new scripts pass `node --check` |
| HTML/local assets | Four pages, unique IDs, one h1 each, 85 local references checked before license snapshot addition |
| Snapshot integrity | Original/copy hashes agree; transport result source hash agrees; 24 site files plus package manifest archived and hash-verified |
| Browser | Desktop and 390×844 mobile checked; no document overflow on all four pages; topic filter counts agree across rows/cards; 25 s video metadata loads without media error |

Repository check failures are preserved, not repaired by rewriting unrelated work or
approving statements. No file under `lean/Challenge/` was edited by this campaign.
`ctrl check` wrote its normal file-backed check results. The unit suite already exceeded
the project's approximate 5-second target before this pass; the new focused tests are fast.

Two UI defects identified during review were fixed: a malformed fragment could throw in
the matrix script, and binary floating-point equality could contradict the boundary-contact
wording. Hash handling now resets incompatible filters, and the calculator reports
“numerical boundary (check exactly)” near equality instead of claiming an admission.

## Scope and environment

The Python experiments use the standard library. The local run used Python 3.14.7;
Lean is pinned to 4.33.1 in this checkout. Manim Community 0.22.0 ran in an isolated
Python 3.12 environment, outside the project dependencies. Its source records the
render command. Poster and mobile/desktop screenshots were visually inspected.

The formal results are polynomial algebra and finite rational weak duality. They do
not establish Python/browser refinement, general bounded-dynamics comparison,
recursive feasibility, sensor calibration, physical braking authority, collision-free
navigation, hardware safety, performance speedups or mathematical novelty.

## Working tree and release state

The checkout was already heavily dirty. During the session another process advanced
HEAD from `96f083c` through `e948639` to `f63bfd34d3347a212e31298b5a53e212ed005e58`,
adding site GIFs and a presentation guide. Those commits and out-of-scope files are
preserved. This campaign made no commit, push, deployment or visibility change.
Checks describe the local state at execution time, not a signed immutable release.

The allowlisted review bundle is `output/ctrl-research-site-2026-10-21.zip` and the
unpacked snapshot is alongside it. The packager excludes unrelated assets/sketches,
private account/budget notes, internal agent history and the rest of the working tree.
Rebuild with:

```sh
uv run python tools/research/build_research_site.py
uv run python tools/research/package_site.py
```

The repo remains private. Existing GitHub Pages is unchanged by this campaign.
The local snapshot serves at `http://127.0.0.1:8766/index.html` while its preview
process is running. Use the saved bundle after that process stops.

## Budget observation

Weekly account usage was 7% at entry and 10% at the final checkpoint in the same
reset window: an observed increase of approximately three percentage points.
This is rounded account-wide usage, including possible activity from other chats,
not an exact bill for this team. The proposed 30-point allowance was a ceiling;
unused allowance is not spent merely to hit it. No continuing automation is installed.

## Assessment

This is a useful research foundation with two bounded demonstrations, not a public
release qualification. Coordinator quality assessment: **B+ / 85%**, subjective.
The biggest remaining gaps are integration fidelity, realistic workload evaluation,
independent human review, and reconciliation of broader repository claims.
