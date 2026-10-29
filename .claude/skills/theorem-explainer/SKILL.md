---
name: theorem-explainer
description: Use when asked to explain, illustrate, animate or write up a theorem from ControlsLean (or any proved result in this repo) for readers. Produces a page under site/explainers/<slug>/ with plain-language text, build-time MathML equations, a theme-aware SVG diagram, two manim animations (simple and harder example), applications and limits, all traced to Lean theorem names.
---

# Theorem explainer

One page per theorem. A reader should leave knowing what the theorem says, why it is true,
what it looks like on a small and a larger example, where it might be useful, and where it
stops. Every claim traces to a Lean theorem or to a number printed by `example.py`.

The reference implementation is `site/explainers/discrete-lyapunov/`. Copy its shape.

## Output layout

```
site/explainers/<slug>/
  explainer.md      # front matter + prose; the only file most edits touch
  example.py        # every number on the page and in the videos comes from here
  diagram.py        # writes diagram.svg (CSS classes, so it follows light/dark)
  diagram.svg
  scenes/*.py       # manim scenes, subclasses of ExplainerScene
  media/*.mp4|png   # rendered; png is the video poster
  index.html        # built, never hand-edited
```

Shared tooling is in `tools/explainer/`: `explainer_style.py` (manim look),
`render.py` (scenes to media), `build.py` (markdown to page, plus checks),
`render_math.mjs` (TeX to MathML via KaTeX at build time).

## Workflow

Track these as tasks. Do them in order; each step's output feeds the next.

### 1. Read the Lean, not the docstring

Open the file and read the exact statement of each theorem you will cite, and the proof's
lemma structure. Write down, before drafting anything:

- **Hypotheses** in plain words, and which ones are unusual (e.g. "P need not be symmetric").
- **Conclusion** exactly as stated. If the docstring claims more than the statement (a rate,
  uniqueness, a bound), the page claims only what the statement proves.
- **Proof skeleton**: the 3 to 5 named lemmas the proof goes through. These become
  "Why it holds".
- **Related theorems** in the repo that use this one or prove its converse
  (`grep -rn "<name>" ControlsLean`). These anchor "Where it might apply".

### 2. Pick two examples and compute them in `example.py`

- **Simple**: the smallest instance where every number can be checked by hand (scalar,
  2x2, n = 2). It should show the mechanism with nothing else going on.
- **Harder**: an instance that shows why the hypothesis or the choice inside it matters,
  ideally one where the naive intuition fails (norm grows while the certificate shrinks;
  the obvious witness fails and the right one works). Include a case where the hypothesis
  fails when that is informative, and say honestly whether the conclusion then fails too.

All numbers live in `example.py` as module constants or functions. Its `__main__` prints
everything the page quotes. Before writing prose, check each claim you intend to make
numerically (monotonicity, bounds, which steps go up). Do not quote a number you have not
printed.

### 3. Draft `explainer.md`

Start from `references/explainer-template.md`. Required front matter: `title`, `subtitle`,
`slug`, `lean`, `theorems` (each must exist in the Lean file), `updated`. Required sections,
in this order, with these ids (`## Heading {#id}`):

| id | Content |
| --- | --- |
| `idea` | 2 short paragraphs and the diagram. The problem first, then the idea. |
| `statement` | Setting, a `theorem-box` with the precise statement, the conditions read plainly, the Lean statement in a code block with a Lean-to-math table. |
| `why` | `<ol class="steps">`, one step per proof lemma, each naming its Lean lemma. One line on which step is the real work. |
| `simple` | Worked numbers, then the first video. |
| `harder` | The instance, the certificate or witness, a short table of steps, the second video. |
| `applies` | `<div class="applies">` cards. Engineering setting, what this theorem certifies there, a repo theorem that uses it if one exists. |
| `limits` | `<ul class="limits">`. Model scope, what it does not compute, floating point, what failing the hypothesis does and does not mean. |
| `check` | Commands to build the Lean file, print the numbers, render, build. |

### 4. Diagram

`diagram.py` writes an inline SVG with `class="diagram"`, `role="img"`, `<title>` and `<desc>`.
Use the CSS classes in `site/explainers/explainer.css` (`level`, `euclid`, `path`, `pt`,
`warn`, `muted-text`, `axis`) instead of hard-coded colors, so it works in light and dark.
Compute geometry from `example.py`. One idea per diagram; a legend beats arrows.

### 5. Animations

Two scenes, about 30 to 60 seconds each. Subclass `ExplainerScene` and use the helpers:

```python
import sys
from pathlib import Path
HERE = Path(__file__).resolve()
sys.path[:0] = [str(HERE.parents[4] / "tools" / "explainer"), str(HERE.parents[1])]
from example import ...
from explainer_style import ACCENT, WARN, BAD, MUTED, ExplainerScene, eq, label, caption

class SimpleCase(ExplainerScene):
    POSTER_AT = 0.45          # fraction of runtime for the poster frame

    def construct(self):
        self.title_card("A plain claim", "model / assumptions")
        self.play(Write(eq(r"x_{k+1} = a\,x_k")))
        self.say("One short caption line at a time.")
        ...
        self.theorem_badge("ControlsLean.Controls.<theorem>")
```

Rules:
- **Computed, not drawn.** Every moving quantity comes from `example.py`. No hand-tuned
  curves.
- **Color means something.** `ACCENT` is the certified object, `WARN` the naive or
  conventional quantity, `BAD` a failed hypothesis, `MUTED` scaffolding. Same in diagram,
  video and page.
- **Honest scales.** One axis scale across cases you compare. Never cap or clip a bar or
  curve to fit; shrink the scale instead.
- **Captions** via `self.say()`: one line, and true for as long as it is on screen (a caption
  quoting "step 1" goes stale by step 8).
- **Badge** via `self.theorem_badge()` names the Lean theorem behind what is on screen. It
  sits in the caption zone; do not call `say()` while it is up.
- **Sans-serif only.** `eq()` uses LaTeX `sansmath`; `label()` uses Inter.

### 6. Render and build

```sh
# media (needs LaTeX with sansmath + dvisvgm, ffmpeg, Inter font)
uv run --no-project --python 3.12 --with manim==0.22.0 --with numpy \
  tools/explainer/render.py <slug> [--quality l|m|h] [--scene Name]

# page + index (needs node; KaTeX installs into tools/explainer on first run)
uv run --no-project --with markdown-it-py --with pyyaml tools/explainer/build.py <slug>
uv run --no-project --with markdown-it-py --with pyyaml tools/explainer/build.py --all --check
```

Use `--quality l` while iterating, `m` (720p) for what you commit. `render.py` picks the
stillest frame near `POSTER_AT`, so posters do not land mid-fade.

### 7. Review what a reader sees

Do not trust the source. Look at the output.

- **Frames**: pull 6 to 8 frames per video into a contact sheet
  (`ffmpeg -ss T -i media/X.mp4 -frames:v 1 ...`, then `tile=2x4`). Check overlaps,
  clipped labels, stale captions, posters.
- **Page**: screenshot in light and dark with a headless browser (Playwright:
  `color_scheme="dark"`). Check math renders sans, brackets stretch, signs are spaced as
  signs, tables and videos fit.
- **Claims audit**: hand the page to the `explainer-auditor` agent. It checks every
  sentence against the Lean statements and `example.py` and reports, without editing.
  Fix what it finds. For a headline page, this pass is not optional.

### 8. Ship

`build.py` regenerates `site/explainers/index.html`. Commit sources, `diagram.svg`, `media/`
and the built `index.html`. Keep each video under about 1 MB at 720p.

## Voice

Humble, clear, technical. The reader is a capable engineer who has not seen this result.

- Lead with the problem the theorem solves, then the idea, then the symbols.
- Short sentences. One idea per paragraph. Define every symbol at first use.
- Say what is proved, by what, and nothing more. "The Lean file proves", not "we show".
- No hype or talking down: avoid *obviously, clearly, trivially, simply, just, easy,
  powerful, elegant, beautiful, remarkable*. `build.py --check` warns on these.
- **No em dashes.** `build.py --check` fails on them. Use a period, a colon or parentheses.
- Applications say "might apply" and name the exact condition under which the theorem
  certifies something there. Do not claim a benefit nobody measured.
- Every limit you know about goes in `limits`, including the ones that make the result look
  smaller.

## Math formatting

- Inline `$...$`, display `$$...$$` on its own lines. KaTeX syntax; macros `\R`, `\N`,
  `\T` (transpose), `\norm{x}` are predefined in `render_math.mjs`.
- Pages ship MathML only, no runtime JS. `build.py` fixes the browser quirks: upright
  multi-letter operators, unspaced norm bars, sign minus after `=` or `,`.
- In `explainer.md`, markdown inside raw HTML blocks is not processed. Inside
  `<li>`/`<div>` use `<strong>` and `<code>`; inline math works anywhere.
- Prefer named constants with subscripts (`c_Q`, `C_P`) over primes.

## Lessons from the pilot

- For exact examples and interactive walkthroughs, use `tools/math_explainers/README.md`.
  SymPy derives/checks the calculation; Manim animates the mechanism; Rough.js shows
  dependencies. `results.json` supplies exact values and binds rendered media to a hash.
  CAS status `unknown` is not a passed check. Keep CAS, finite tests and Lean evidence distinct.
- Manual/timed walkthroughs may be embedded as an optional iframe. The theorem body still
  renders statically with build-time MathML. Use `?embed=1`, a descriptive iframe title,
  lazy loading, and the accessible shared player. Keep assumptions in both the page and captions.
- A ratio rounded for display is not an exact extremum. Non-normality alone does not imply
  transient norm growth; check the operator norm against 1 as well as the spectral radius.

- `‖x‖` on `n → ℝ` in Mathlib is the **sup norm**, not Euclidean. Constants the proof
  produces (rates, bounds) differ from the textbook Euclidean ones. Say which norm, and do
  not quote a Euclidean constant as "the proof's".

- A docstring said "converges geometrically"; the theorem states convergence only. The page
  says the rate is a separate theorem and is existence-only.
- "The plain error can grow" is false for gradient descent on a symmetric quadratic
  (the iteration matrix is symmetric, so its norm equals its spectral radius). It is true for
  Jacobi or heavy-ball. Check application claims as carefully as the math.
- Capped bars made a growing quantity look flat. Uncapped linear scale fixed it.
- Sans-serif math on the web needs `mi { text-transform: none }`, or browsers fall back to a
  serif math-italic font. Stretchy brackets need a math font; `explainer.css` handles both.
