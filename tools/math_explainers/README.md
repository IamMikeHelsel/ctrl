# Math explainers and experiment lab

SymPy supplies exact calculations. Manim explains mathematical mechanisms. Rough.js draws
relationships and counterexamples. A shared player supports manual and timed steps.

The lab extends the discrete-Lyapunov pilot from PR #38 and the existing delayed-braking
study. It preserves the distinction between existing Lean results, new CAS calculations,
finite experiments, executable refinement, timing, and physical validation.

## Reproduce

Requirements: uv, Node 20+, Manim Community 0.22.0, FFmpeg and ffprobe. The new Manim scenes
use Arial/Pango, so they do not need LaTeX. The older pilot scenes retain their original
LaTeX/font requirements. On this development machine the existing Manim executable was used;
install it following [Manim's platform instructions](https://docs.manim.community/en/stable/installation.html).

```sh
uv sync --group dev
uv run experiments/math_explainers/run.py
uv run python -m pytest -q tests/test_math_explainers.py
uv run python tools/math_explainers/render.py
npm ci --prefix tools/math_explainers
npm run build --prefix tools/math_explainers
uv run --no-project --with markdown-it-py --with pyyaml tools/explainer/build.py --all
uv run --no-project python -m http.server 8145 --bind 127.0.0.1 --directory site
```

Open `http://127.0.0.1:8145/explainers/lab/`. The runner pins SymPy 1.14.0. Package-lock pins
Rough.js 4.6.6 and resvg 2.6.2. Experiments take seconds and make no network or model API calls.
All generated pages are static and have no runtime CDN dependency.

## What is shared

- `experiments/math_explainers/run.py`: eight bounded experiments; exact fractions, explicit
  hypotheses, negative controls, source links, and next tests with rejection criteria.
- `site/explainers/lab/results.json`: generated evidence and display data. Numeric entropy
  and display coordinates are explicitly approximate; witnesses and rational calculations
  retain exact values. Unknown CAS zero checks are rejected.
- `scenes/math_scenes.py`: three four-section animations. Each manifest records the result
  artifact's SHA-256. `render.py --scene LyapunovWalkthrough` renders one scene.
- `stories.mjs`: four complete-state organic diagrams. Add a story with explicit `show` and
  optional `focus` lists for every step. `src/sketch.mjs` validates references and escapes text.
- `web/player.js`: shared playback controller; `web/player.css`: responsive presentation.
- `build.mjs`: source/artifact/video hash gates, static gallery, players, SVG/PNG exports.

The hash gates reject changed experiment source, tampered results, and stale videos before
writing outputs. Re-run the experiments and render affected scenes after changing the data.
The generated pages include their fonts and media and can be saved as standalone HTML.
The gallery itself needs its adjacent files.

## Embed and control

Use any player URL with `?embed=1` in a website or Google Sites iframe. Use exported PNGs in
Docs/Slides, or upload MP4s to Drive and insert them into Slides. Docs and Slides do not run
the interactive JavaScript player inside a document or slide. See Google's
[Sites embed guide](https://support.google.com/sites/answer/90569?hl=en) and
[Slides image/video guide](https://support.google.com/docs/answer/97447?hl=en).

`window.diagramPlayer` exposes `goTo(index)`, `next()`, `previous()`, `play()`, `pause()`,
`setSpeed(0.5|1|1.5|2)`, and `getState()`. Steps are zero-indexed. Window events are
`diagram:stepchange`, `diagram:play`, `diagram:pause`, and `diagram:end`. Scripts in a parent
page can access this API only for a same-origin frame. There is no cross-origin message API.
Keyboard arrows, Home/End and Space are available. Reduced motion uses video posters;
timed traversal occurs only after an explicit Play action. Hidden documents pause playback.

## Sources and scope

Tao's equational-theories project inspires finite countermodel search; Green, Manners and
Tao's sumset/entropy work inspires support-growth questions; Tao's Blueprint tour inspires
visible dependencies. These are methodological connections, not claims that PFR proves
anything about the simulated robot or that Tao proposed these experiments.

OpenAI/math is pinned at `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`, verified against its
repository head on 28 October 2026. The tropical fixture checks the displayed feasible-point
cost gap, not the substitution algorithm. The scheduling experiment adopts the three-machine
unit-job specification and uses our own tiny BFS, not the upstream algorithm or complexity
proof. This suite does not replay any upstream Lean proof. Exact source URLs are in the JSON.

The 3,924 cases are declared experimental cases with different domains, not independent
statistical trials or proof counts. Successful tests do not establish general performance,
runtime behavior, probabilistic calibration, or hardware safety.

## Attribution

AI-assisted experiment design, implementation, explanations, and independent claims review.
Original existing theorem exposition is preserved and corrected where reviewed. Toolkit code
is under the repository MIT license. Rough.js and resvg are MIT-licensed dependencies; Manim
is MIT, SymPy is BSD-3-Clause. Kalam is SIL OFL 1.1; its license is in `assets/Kalam-OFL.txt`
and embedded in exported SVG font styles. Source mathematics is attributed in the report;
OpenAI/math is Apache-2.0 and no upstream Lean source is redistributed in this lab.
