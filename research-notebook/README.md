# Controls and mathematics research notebook

This folder preserves the research from the local Codex workspace started on 16 October 2026.
It includes proofs, drafts, source notes, failed approaches, comparison data, review records,
and final animations. Start with the reports below.

| Area | Start here |
|---|---|
| Finished tracking through finite replans | [Five-page note](publication/tracking-note/main.pdf), [proof scope](research/adjacent-controls/tracking-replans/README.txt), [Manim video](research/adjacent-controls/tracking-replans/animation/changing-plans.mp4) |
| Motion continuity when plans change | [Next proof](research/adjacent-controls/tracking-replans/trajectory-damper-next-step.txt), [industrial baselines](research/adjacent-controls/tracking-replans/industrial-motion-baselines.txt), [seven further checked statements](research/adjacent-controls/tracking-replans/smoothing-verification.json) |
| Tonight's closure across tracks | [Status](research/tonight-closure/README.txt), [Erdős conditional formalization note](research/tonight-closure/erdos-formalization-note.txt) |
| Human steadiness and VLA target decisions | [Report](research/adjacent-controls/steady-motion/index.html), [proof scope](research/adjacent-controls/steady-motion/README.txt), [Manim video](research/adjacent-controls/steady-motion/animation/steady-enough.mp4) |
| Changing response, stopping, and holding | [Report](research/adjacent-controls/variable-response/sampled-handoff/index.html), [proof scope](research/adjacent-controls/variable-response/README.txt) |
| Smooth motion under replanning | [Proof and comparison](research/adjacent-controls/vla-smooth-replanning/report.txt), [animation](research/adjacent-controls/vla-smooth-replanning/animation/smooth-replanning.mp4) |
| Main Lean controls project | [README](lean-controls/README.txt), [pinned toolchain](lean-controls/lean-toolchain) |
| Paper drafts and frozen evidence | [Current-paper guide](publication/README.txt), [manuscript](publication/robust-manuscript/main.pdf) |
| Erdős and prize opportunities | [Assessment](research/opportunity-assessment/current-status.html), [Erdős conditional theorem](research/opportunity-assessment/erdos-completion-spike/FINAL-STATUS.txt) |
| Geometric Unity mathematical audit | [Report](research/weinstein-lean/operator-audit/report.txt), [independent review](research/weinstein-lean/operator-audit/independent-review.txt) |

GitHub shows the source of HTML reports. Open them from a local checkout for the formatted page.
The papers and animations also have direct file links. Nothing in this import submits a paper,
claims a prize, or establishes publication novelty.

## Evidence and toolchains

This notebook is separate from the root `ControlsLean` library. Its main project uses Lean 4.35.0;
the root library currently uses a different pin. Keep the notebook's `lake-manifest.json` and
`lean-toolchain` files unchanged when replaying its evidence. Importing these files does not make
them part of the root build or its CI coverage.

The tracking package contains 34 checked statements, including helper lemmas, plus a 144-case
numerical comparison and independent critique. A separate seven-statement followup checks the
cost of bounded command-filter error and limits on continuity at replans. It does not yet prove
a filter keeps that error bound. The earlier steadiness package contains 16 checked
theorem statements. Each package preserves its verifier, source hashes, axiom audit,
kernel replay logs, and rejected false mutations.
Other folders have their own scopes and verification records. Some contain incomplete attempts
and deliberate negative tests. A count of `.lean` files is not a count of proved results.

The original files are copied byte-for-byte. In particular, no theorem, source claim, negative
result, or verification record is rewritten to fit this repository. AI assistance and open
questions remain disclosed in the source reports. Imported material retains its source and license
notices; the repository's software license does not relicense downloaded papers.

## Update and check

From the repository root:

```sh
python3 tools/sync_research_notebook.py --source /path/to/working-research-folder
python3 tools/sync_research_notebook.py --source /path/to/working-research-folder --check
python3 -m unittest discover -s tests -p test_research_sync.py -v
```

The first command updates this notebook. The second fails if new or changed source files have not
been copied. Both check every recorded hash. They preserve executable permissions, refuse to
overwrite independent edits in this folder, and retain historical files removed from the source.
Review the diff, commit it, and push the research branch. Check remote state before reporting that
new work is backed up.

The working source is recorded in [`_sync/manifest.json`](_sync/manifest.json). That file records
1,340 imported files in the first snapshot. Future snapshots may contain more files.
The checked import excludes installed tools, `.lake` caches, Python caches, compiled Lean objects,
Manim intermediate render caches, and LaTeX scratch output. Final videos, frames, papers, source
archives, data, and proof logs are retained. A notebook copy does not include a preinstalled Lean
or Python runtime; follow each project's setup instructions before running its proof verifier.

## External repositories

Twelve downloaded repositories are recorded in
[`_sync/nested-repositories.json`](_sync/nested-repositories.json), with exact source URLs and
commits. Their complete clean checkouts and Git object stores are not vendored. Local changes are
preserved under [`_sync/overlays`](_sync/overlays): binary-capable tracked-file patches plus copies
of untracked research files. This includes the SOS comparison experiments and local verifier
adaptations.

To reconstruct an external checkout, clone its recorded source to the recorded relative path,
check out the recorded commit, apply its `working-tree.patch` if present, then copy the contents of
its overlay's `untracked/` folder into that checkout. Install dependencies separately. Check the
source project's license and instructions before reusing its code.
