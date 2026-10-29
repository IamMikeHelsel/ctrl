# Verification, 28 October 2026

This records local validation of the math-explainer update, not deployment or hardware acceptance.

| Check | Result |
| --- | --- |
| Experiment runner | Eight completed experiments, 3,924 declared cases; deterministic JSON |
| Focused independent-oracle tests | 7 passed |
| Full repository Python suite | 74 passed, 1 integration test deselected |
| Full Lean build, escape-hatch scan and axiom audit | `scripts/check.sh` passed: 55 files, 445 headline theorems; existing linter warnings remain |
| Explainer content checker | Required sections, theorem names, source references and MathML passed |
| New Manim media | Three videos, 12 sections, 1280 × 720; complete videos each below 1 MB |
| Media review | Eight-frame contact sheets for every new video; no clipping, overlap or stale step-specific captions found |
| Browser playback | All seven players: Next, keyboard Back, speed 2×, timed completion and stop |
| Layout | All players and four integration pages fit a 430 × 932 viewport without document overflow |
| Embedding and accessibility | In-page iframe navigation, embed mode, and reduced-motion poster behavior passed |
| Downloads | SVG, PNG and MP4 downloaded; video playback succeeded with network disabled |
| Artifact integrity | Changed source, tampered JSON and stale video fingerprints rejected before output mutation; generated manifest hashes verified |
| Local links | 123 relative references across explainers and changed site pages resolved |

Commands are in `README.md`. Test commands use `uv run python -m pytest` to bind pytest to
the selected interpreter. One early editable-install/entrypoint failure was resolved by
reinstalling the local package; the full suite then passed.

An independent AI reviewer read the exact Lean statements and separately reproduced the
Stein identity, all 14 energy losses, the braking sweep using subinterval integration,
saturation counts, all 127 three-step reachable sets, and all 1,024 five-job scheduling
optima using slot-assignment enumeration. It checked the OpenAI fixture against the pinned
model. Review corrected three inherited prose issues: asymptotic versus ordinary stability,
rounded versus exact contraction rate, and the condition for transient norm growth.

The existing Lyapunov page's mobile table overflow was found in the browser and fixed with
scrollable table regions. Query-string local links are now checked by URL path. One existing
braking-sketch source needed formatting to satisfy the repository's blocking formatter.

Browser evidence is Chromium on macOS, including desktop light and mobile dark screenshots.
Safari, Firefox, physical mobile devices and actual Google Workspace embedding were not
tested. The two original pilot videos were rerendered after review found a stale caption
when switching the scalar example from stable to unstable. Captions now fade sequentially,
and the planar video's rounded contraction label uses an approximation sign. Three new
sectioned videos were rendered as well.
New experiments do not add Lean theorems, replay OpenAI's proofs or establish controller,
RTOS, actuator or physical safety properties. Finite case counts are not statistical trials.

Local diagnostic logs and contact sheets are under ignored `output/math-explainers/`.
Public generated files and their hashes are listed in `site/explainers/lab/manifest.json`.
