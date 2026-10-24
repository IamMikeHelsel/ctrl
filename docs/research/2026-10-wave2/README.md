# Research wave 2 (2026-10-24): where we can make progress

Wave 1 (`docs/RESEARCH_FRONTIER_2026-10.md`) scouted 76 candidates. Wave 2 ran six lanes that produce artifacts instead of surveys: a math retrieval index, a scout for it, a numerical attack on Byers–Nash n = 6, an audit of the claimed Erdős results, a test of whether cloud sessions can run Lean, and proof blueprints for the four best Lean targets. Every report in this directory says what was verified and what was not.

## What changed

1. **Lean can run in cloud sessions after one allowlist entry.** The pinned toolchain (v4.36.0-rc1) and all Lake dependencies install from GitHub release assets in about 46 s. Only the Mathlib `.olean` cache is blocked. Add `cache.mathlib.org` under the environment's allowed domains and use `scripts/setup-lean-cloud.sh` as the setup script. Without it, building Mathlib from source here takes an estimated 4–8 hours. Report: [`LEAN_IN_CLOUD.md`](LEAN_IN_CLOUD.md).
2. **Byers–Nash n = 6 is open, but the documented proof plan does not work.** No n = 6 counterexample turned up in 144 SDP-dual ascents. The n = 7 counterexample re-verifies exactly (s² < 1196 < k²). The "single remaining cross-term inequality" is false: exact rational certificates show no argument built from the existing comparator families can reach k ≤ s. `STATUS_AND_ROADMAP.md` also defines s and k as minima, and that version is false already at n = 3. The repo's Lean targets the maxima. Report: [`BYERS_NASH_N6.md`](BYERS_NASH_N6.md), verifiers in [`bn6/`](bn6/).
3. **Most of the claimed Erdős list does not hold up.** Of 31 claimed numbers, 3 are worth linking now (834 exact, 1148 and 367 variants), 7 were formalized by others, 4 are variants only, and 17 have no ctrl proof of any Formal Conjectures statement. Nothing is eligible for the Justin Sun Prize. Report: [`ERDOS_CLAIMS_AUDIT.md`](ERDOS_CLAIMS_AUDIT.md).
4. **Four Lean targets now have blueprints ready to execute.** Each blueprint gives statements in ctrl's style, a lemma DAG, and every Mathlib lemma checked against the source. Ranked by value times odds of finishing in two weeks: the H∞ filter (5–7 days), geometric SO(3) tracking (8–11 days), Willems' lemma (7–10 days), and the easy direction of KYP (3–4 days). The full KYP converse needs a spectral theorem Mathlib lacks. Report: [`BLUEPRINTS.md`](BLUEPRINTS.md), numerics in [`blueprint-numerics/`](blueprint-numerics/).
5. **The math retrieval index is built and works offline.** `tools/mathdb/` indexes 302,429 records from six sources: Mathlib (275,738 declarations and module docs), formal-conjectures (11,875), openai/math (9,337), ctrl across three branches (3,186), Erdős metadata (1,221) and JSP (1,072). The default needs only Python and numpy. It runs BM25 fused with character n-grams, answers a warm query in about 150 ms, and rebuilds in about 6 minutes. On the public LeanSearch-v2 benchmark it scores half of LeanSearch v2's published figure, because there are no dense vectors for Mathlib yet. Every prebuilt Mathlib index sits on blocked hosts. The Qwen3-Embedding models are reachable from Docker Hub, but CPU embedding here is about 1.3 s per passage, so only ctrl and the Erdős records got a dense channel. Embedding all of Mathlib on one GPU is about an hour, and the vectors drop in by record id. Reports: [`MATHDB_BUILD.md`](MATHDB_BUILD.md), [`MATHDB_SCOUT.md`](MATHDB_SCOUT.md), eval tables in [`mathdb-eval/`](mathdb-eval/).

| benchmark | retriever | nDCG@10 | Recall@10 |
| --- | --- | ---: | ---: |
| LeanSearch-v2 MathlibQR, 946 queries | BM25 | 0.310 | 0.434 |
| same | keyword hybrid (default) | 0.303 | 0.426 |
| same | LeanSearch v2, published | 0.623 | — |
| own 112-query set | keyword hybrid | — | 0.670 |
| same | keyword hybrid + Qwen3 channel | — | 0.688 |

The published LeanSearch v2 figure comes from search summaries of the paper and was not re-run here.

## Corrections to wave 1

- The research code is on `origin/crossover-research-2026-10-19`, and RoboLean is on `origin/backup/20261020/dev-ctrl/snapshot`. Wave 1 said both were missing.
- The repo is public, not private.
- plby holds only partial results for Erdős 291 and 367, not ctrl's statements.
- Mathlib does have PSD Schur-complement lemmas (`Matrix.PosSemidef.fromBlocks₁₁`, `fromBlocks₂₂`) and a rank-one PSD decomposition.
- The Byers–Nash "90% complete" status is withdrawn.

## Suggested order

| step | candidate | effort |
| --- | --- | --- |
| Allowlist `cache.mathlib.org`, adopt the setup script | `TOOL-13` | minutes, user action |
| Link Erdős 834 in Formal Conjectures, fix the claimed counts in README and STATUS | `MATH-06` | 1 week |
| KYP easy direction next to `BoundedRealHInf.lean` | `MATH-07` | 3–4 days |
| H∞ filter | `EST-05` | 5–7 days |
| Geometric SO(3) tracking | `ROB-01` | 8–11 days |
| Willems' lemma and DeePC | `EST-04` | 7–10 days |
| Publish the index as a release asset, GPU-embed Mathlib, add an MCP server | `TOOL-14` | 1 week |

`./ctrl synergy next -b 6` reproduces this ordering from `docs/SYNERGY_WEIGHTS.json`.

## Edits these findings imply, not made here

`README.md` and `docs/STATUS_AND_ROADMAP.md` still claim 25–29 solved Erdős problems and describe Byers–Nash n = 6 as 90% proved with one cross-term left. `STATUS_AND_ROADMAP.md` also defines s(A) and k(A) as minima. These are the maintainer's headline claims, so this wave flags them rather than rewriting them.
