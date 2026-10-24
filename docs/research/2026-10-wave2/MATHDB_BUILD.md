# MATHDB-BUILD: a local math retrieval index (wave 2)

Date: 2026-10-24. Nothing was committed or pushed. All numbers below come from runs in this container (4 vCPU, shared).

## 1. Summary

- A working offline index now covers 302,429 records:
  - every Mathlib declaration, including module docs;
  - ctrl theorems from 3 branches, deduplicated;
  - formal-conjectures statements with category and formal_proof links;
  - Erdős, JSP and plby metadata;
  - OpenAI-math manuscripts: titles, abstracts and theorem-like LaTeX environments.
- Query: `python3 tools/mathdb/query.py "..." -k 10 [--source ...] [--json]`. It needs the system python3 with numpy only.
  - Cold CLI call: 0.4-0.6 s.
  - Warm hybrid search: median about 170-200 ms.
- Retrieval quality is lexical-grade, not semantic-grade.
  - On the LeanSearch-v2 MathlibQR benchmark (946 queries), the best channel is BM25 with nDCG@10 = 0.310 and Recall@10 = 0.434.
  - The published LeanSearch v2 nDCG@10 is 0.623 (coordinator-supplied figure; I did not verify it myself).
  - On our own 112-query labelled set, the default `hybrid2` (BM25 + char n-gram RRF) gets R@10 = 0.670 and MRR@10 = 0.385.
- Dense models:
  - **WordLlama**, the only PyPI wheel that ships weights, does not help. Alone it is the worst channel. Fused in, it is mixed: it helps natural-language Mathlib queries and hurts ctrl queries.
  - **Qwen3-Embedding-0.6B** (GGUF from Docker Hub `ai/`, via llama-cpp-python) is now an optional channel over the 3,543 ctrl theorems/lemmas and Erdős records. It clearly helps there:
    - ctrl: MRR@10 0.62 → 0.83 alone, R@10 1.00;
    - Erdős prose (strict): R@10 0.50 → 0.78.
    - Fused as `hybridq`, it lifts the overall labelled-set MRR from 0.385 to 0.427.
  - On this CPU Qwen3 costs ≈1.25 s per passage, so it cannot cover Mathlib here.
  - model2vec and fastembed cannot get weights here; both fail on the Hugging Face proxy block (403).
- CLI default is `auto`: `hybridq` if the optional Qwen channel is installed, else `hybrid2`. The PyPI-only path is unchanged.

## 2. Deliverables

| what | where |
|---|---|
| parser | `/home/user/ctrl/tools/mathdb/lean_parse.py` |
| build pipeline | `/home/user/ctrl/tools/mathdb/build.py` |
| query CLI / library | `/home/user/ctrl/tools/mathdb/query.py` (`MathDB` class) |
| evaluation | `/home/user/ctrl/tools/mathdb/eval.py`, with `make-queries`, `run` and `leansearch` subcommands |
| labelled queries | `/home/user/ctrl/tools/mathdb/eval/queries.jsonl` (112) and `/home/user/ctrl/tools/mathdb/eval/holdout_ids.txt` (40) |
| optional Qwen3 channel | `/home/user/ctrl/tools/mathdb/embed_qwen.py` |
| shared helpers | `/home/user/ctrl/tools/mathdb/common.py`: tokenizer, symbol glossary, RRF, WordLlama offline loader |
| docs | `/home/user/ctrl/tools/mathdb/README.md`: rebuild commands, pins, index layout, known gaps |
| built index | `~/.cache/ctrl-mathdb/index (built in-session; not committed)/` |
| eval index | `(session scratch eval index)/` (40 held-out docstrings removed) |
| raw results | `(session scratch)/{eval-results2.md,eval-results2.json,leansearch-results2.md,leansearch-results2.json}` |
| build venv | `(session venv)/` (numpy 2.5.4, PyYAML 6.0.3, wordllama 0.4.0.post1, rank-bm25, scikit-learn, sqlite-vec) |

Notes on the code:
- In the build venv, rank-bm25, scikit-learn and sqlite-vec were installed for probing. They are not used by the shipped code.
- The shipped code uses SQLite FTS5 bm25() plus numpy only. There are no extra runtime dependencies for the default mode.

## 3. Corpus counts (main index, built in 380 s)

| source | records | details |
|---|---|---|
| mathlib (0b57f69) | 275,738 | 267,247 declarations and 8,491 module docs |
| ctrl | 3,186 | from 4,485 raw rows before dedupe. Working tree + `origin/crossover-research-2026-10-19` + `origin/backup/20261020/dev-ctrl/snapshot`, deduped by (name, module); later copies are noted in `extra.also_in` |
| fc (c094b97) | 11,875 | 1,672 modules |
| erdos | 1,221 | erdos.json ∪ plby (563 entries in sources.yaml). Fields: status, prize, FC category, has_formal_proof, plby URLs, JSP ids and JSP titles, FC main docstring |
| jsp | 1,072 | rows mapped to an Erdős problem carry the FC file path |
| openai (1581d4c) | 9,337 | 372 families, 719 manuscripts, 8,246 theorem/proposition/corollary/conjecture environments (at most 40 per manuscript) |

Kind and docstring breakdown:
- **mathlib:** 130,434 theorem, 61,625 lemma, 33,893 def, 27,908 instance, 5,593 alias, 3,705 abbrev, 2,022 class, 1,718 structure, 347 inductive. 82,740 records have a docstring.
- **ctrl:** 2,001 theorem, 321 lemma, 661 def.
- **fc:** 6,797 theorem, 620 lemma, 2,476 def.

License tags are stored per record:
- Mathlib, formal-conjectures and openai/math: Apache-2.0.
- ctrl: MIT per the repo LICENSE. File headers say "Apache 2.0", which is an inconsistency in ctrl itself.
- Erdős and JSP metadata: upstream terms not verified.
- LeanSearch-v2's benchmark, used only for evaluation: Apache-2.0.

## 4. Parser accuracy

The parser is a regex/line parser and needs no Lean toolchain. It blanks nested comments, keeps strings, tracks namespace/section/end/mutual, attaches docstrings across attribute blocks, and handles `alias ⟨a, b⟩ := iff`, `@[to_additive explicitName]`, `irreducible_def` and universe-annotated names.

- **Grep cross-check (Mathlib).** A keyword-at-line-start grep over comment-blanked code finds the same declaration lines as the parser, apart from about 3 stray lines. The first version missed 1,399 `alias ⟨…⟩` tuple lines; that is now fixed.
- **formal-conjectures vs `tools/data/fc.json`** (independent list of 2,798 Erdős theorem names, rev e754a78, older than our c094b97):
  - 2,776/2,798 (99.2%) match by the `N/short_name` key. The other 22 are also present but under nested namespaces (e.g. `Erdos107.variants.ersz_bounds`); fc.json strips that namespace. So name recovery is 100% modulo naming convention.
  - Category agrees on 2,760/2,776. All 16 disagreements are open→solved changes between the two revisions.
  - The formal_proof flag agrees on 2,740/2,776. The differences are links added upstream after e754a78.
- **LeanSearch-v2 gold names.** 191/200 gold declarations exist verbatim in our index (181 before the parser fixes for universes, `irreducible_def` and anonymous instances). The 9 still missing are:
  - 3 cases where the benchmark's namespace differs from Mathlib HEAD (e.g. gold `CategoryTheory.FundamentalGroupoid`, but the source defines root `FundamentalGroupoid`);
  - 1 structure field (`GCDMonoid.gcd_mul_lcm`, a projection);
  - about 5 auto-generated anonymous-instance names, which are only approximated.
- **Manual spot checks** (2 random samples of 30 Mathlib declarations each, compared against source lines):
  - Sample 1 (before fixes): 26/30 fully correct. 2 docstrings were missed because the nearest `/-- -/` was the to_additive doc inside the attribute (fixed). 2 anonymous-instance names were wrong (heuristic improved).
  - Sample 2 (after fixes): 29/30 fully correct. One signature is truncated: a `letI … :=` inside the type stops the `:=` scan.
- **Known gaps:**
  - About 15,100 declarations whose additive twin comes from `@[to_additive]` without an explicit name. Those auto-translated names are not generated. 1,182 explicit names are generated.
  - `@[simps]`/`deriving` names and structure projections.
  - Macro-generated declarations other than `irreducible_def`.
  - `variable` binders are not added to signatures.
  - Anonymous instance names are heuristic. Of the 2,054 distinct `inst*` identifiers referenced in Mathlib source, 1,884 (91.7%) resolve to an index name by last component (1,847 before the heuristic rewrite).

## 5. Embedding options actually tried

| option | result |
|---|---|
| wordllama 0.4.0.post1 (PyPI) | **Works offline.** The 256-d `l2_supercat` weights and tokenizer ship in the wheel (32 MB). Version 0.4.0 has a path bug (it looks in `tokenizer/` but ships `tokenizers/`); the workaround is `cache_dir=<pkg dir>, disable_download=True` in `common.load_wordllama`. It embeds 302k records in 146 s on CPU |
| model2vec (`minishlab/potion-base-8M`) | Fails: HF ProxyError 403 |
| fastembed (`BAAI/bge-small-en-v1.5`) | Fails: HF 403, then the GCS fallback also fails ("Could not load model … from any source") |
| Qwen3-Embedding-0.6B Q8_0 GGUF (scout-fetched from Docker Hub `ai/`) | Works with llama-cpp-python (scout-built venv). About 70 tokens/s with 3 threads uncontended, 1.25 s per 90-token passage. All of Mathlib (≈300k passages) would take ≈4 CPU-days here, so only the small corpora were embedded |
| corpus-trained LSA (TF-IDF + SVD) | Script written (`scratchpad/lsa_experiment.py`) but **not run**; time went to the benchmark and Qwen. No result to report |
| sqlite-vec 0.1.9 | Installs and loads cleanly. Not needed, because brute-force numpy over 302k×256 takes about 20-45 ms |

## 6. Retriever comparison

Retrievers compared:
- `bm25`: FTS5 bm25 over identifier-aware tokens, with name weight 3 and body weight 1.
- `char`: TF-IDF cosine over hashed word-boundary char 3-5-grams.
- `dense`: WordLlama.
- `hybrid2`: RRF(bm25, char), the default.
- `hybrid`: RRF(bm25, char, WordLlama).

Exact-name and Erdős/JSP-number shortcuts are part of `search()`, but none of the eval queries trigger them.

### 6a. Own labelled set (112 queries; eval index with the 40 held-out docstrings removed; k=10)

The groups are:
- `mathlib_heldout`: 40 random Mathlib docstrings, with the target's own name stripped from backticks, used as the query for that declaration.
- `mathlib_nl`: 28 hand-written names of classical theorems ("Bolzano-Weierstrass…", "Wilson's theorem…").
- `ctrl_nl`: 26 hand-written control/estimation/robotics/vision paraphrases, e.g. "discrete algebraic Riccati equation uniqueness under detectability" → `dare_unique_of_detectable`.
- `erdos_prose`: 18 hand-written Erdős problem paraphrases → `FormalConjectures/ErdosProblems/N.lean`. A hit is any result whose path is that file. `erdos_prose_strict` counts only fc and erdos rows, not JSP rows.

| group | metric | bm25 | char | dense | **hybrid2** | hybrid |
|---|---|---|---|---|---|---|
| mathlib_heldout (40) | R@1 / R@5 / R@10 | .025/.275/.450 | .025/.225/.425 | .000/.050/.125 | .025/.300/.450 | .025/.250/.400 |
| | MRR@10 | .127 | .132 | .037 | **.155** | .124 |
| mathlib_nl (28) | R@1 / R@5 / R@10 | .250/.786/.786 | .321/.571/.714 | .250/.393/.536 | .286/.750/.786 | .357/.679/.857 |
| | MRR@10 | .432 | .423 | .316 | .463 | **.508** |
| ctrl_nl (26) | R@1 / R@5 / R@10 | .423/.808/.923 | .308/.731/.769 | .077/.154/.269 | .462/.808/.923 | .192/.692/.885 |
| | MRR@10 | .600 | .465 | .117 | **.618** | .398 |
| erdos_prose (18) | R@1 / R@5 / R@10 | .389/.500/.500 | .444/.500/.611 | .333/.444/.556 | .389/.556/.611 | .333/.500/.556 |
| | MRR@10 | .428 | **.478** | .385 | .437 | .423 |
| erdos_prose_strict (18) | R@10 / MRR@10 | .389/.250 | .556/.385 | .444/.274 | .500/.317 | .500/.349 |
| **ALL (112)** | R@1 / R@5 / R@10 | .232/.562/.652 | .232/.473/.607 | .134/.223/.330 | **.250/.571/.670** | .196/.500/.652 |
| | MRR@10 | .361 | .337 | .181 | **.385** | .331 |

Caveats on this set:
- The hand-written groups were written by me after looking at the target corpora, which risks favourable bias. I paraphrased rather than copied, but the numbers are optimistic for the ctrl and Erdős groups.
- Linking JSP titles into the Erdős records was done after a first eval run. It raised strict Erdős R@10 for hybrid2 from 0.444 to 0.500. This is data integration (independent one-line restatements), not query-specific tuning, but it was motivated by the eval.

### 6b. LeanSearch-v2 MathlibQR (external; 200 gold declarations × up to 6 query styles = 946 queries; `--source mathlib`; k=10; main index)

| scope | metric | bm25 | char | dense | hybrid2 | hybrid |
|---|---|---|---|---|---|---|
| all 946 queries | nDCG@10 | **.310** | .209 | .189 | .303 | .309 |
| | R@10 | .434 | .308 | .267 | .426 | **.442** |
| | R@1 / MRR@10 | .198/.271 | .123/.178 | .124/.165 | .196/.265 | .191/.268 |
| gold exists at HEAD (903 queries) | nDCG@10 / R@10 | .325/.455 | .219/.322 | .198/.280 | .318/.446 | .324/.463 |

nDCG@10 by query style (all 946):

| style | bm25 | hybrid2 | hybrid |
|---|---|---|---|
| q1a_lean (199) | .416 | .341 | .406 |
| q1b_latex (200) | .240 | .252 | .259 |
| q1c_natural (199) | .365 | .393 | .369 |
| q2_slogan (197) | .321 | .312 | .313 |
| q3_nickname (128) | .195 | .203 | .170 |
| q4_special_case (23) | .070 | .127 | .144 |

Reference figures, supplied by the coordinator from search summaries and not checked by me: LeanSearch v2 nDCG@10 = 0.623, next best 0.533. Our best (0.310) is about half of LeanSearch v2. Their pipeline uses LLM informalization plus a trained or large embedding model; ours is lexical.

**Choice of default.** Among PyPI-only settings, hybrid2 wins our labelled set, and on MathlibQR it is within 0.007 nDCG of bm25 and hybrid, which is noise at n=946. It needs neither wordllama nor a model load. The CLI default `auto` therefore resolves to `hybrid2` unless the optional Qwen channel is installed (section 7).

## 7. Optional Qwen3 channel (ctrl theorems/lemmas + Erdős records, 3,543 passages)

Setup:
- Model: Qwen3-Embedding-0.6B-Q8_0.gguf, last-token pooling, 1024-d.
- Passages use the recipe "short name: doc[:320] statement[:200]".
- Queries are prefixed with an instruction and embedded with `n_threads=1`.
- Embedding the 3,543 passages took 4,396 s at 3 threads, partly contended (≈70 tok/s once uncontended). Total wall time including an earlier interrupted run was ≈1.6 h.
- Stored files:
  - `emb_qwen3.npy`: 14.5 MB.
  - `emb_qwen3_ids.json`: record ids. The query side joins on these, so the vectors survive rebuilds and externally computed vectors can be dropped in.
  - `emb_qwen3.json`
- To run it: `MATHDB_QWEN_GGUF=<gguf>` plus a python that has llama-cpp-python. The scout venv `mathdb-scout/bench/venv` works.

Same 112-query eval index (`qwen` alone can only return ctrl and Erdős rows, so it scores 0 on the Mathlib groups by construction):

| group | metric | bm25 | char | hybrid2 | qwen | **hybridq** = RRF(bm25, char, qwen) |
|---|---|---|---|---|---|---|
| mathlib_heldout (40) | R@10 / MRR@10 | .450/.127 | .425/.132 | .450/.155 | 0/0 | .425/.152 |
| mathlib_nl (28) | R@10 / MRR@10 | .786/.432 | .714/.423 | .786/.463 | 0/0 | .786/.438 |
| ctrl_nl (26) | R@1 / R@10 / MRR@10 | .423/.923/.600 | .308/.769/.465 | .462/.923/.618 | **.731/1.000/.827** | .615/1.000/.764 |
| erdos_prose_strict (18) | R@1 / R@10 / MRR@10 | .167/.389/.250 | .278/.556/.385 | .222/.500/.317 | .389/**.778**/.505 | **.500**/.667/**.535** |
| ALL (112) | R@1 / R@10 / MRR@10 | .232/.652/.361 | .232/.607/.337 | .250/.670/.385 | .232/.357/.273 | **.295/.688/.427** |

Latency, warm, while nothing else was running:

| retriever | median ms | p95 ms |
|---|---|---|
| qwen | 561 | 1,059 |
| hybridq | 730 | 1,578 |

Most of that is the CPU query embedding. A cold CLI call adds about 1-9 s for model load.

Interpretation:
- Qwen3 is clearly better than the lexical channels on paraphrased ctrl and Erdős queries. On ctrl it moves MRR from 0.62 to 0.83, and it ranks first on 19/26 queries versus 12/26.
- Fusing it costs Mathlib NL queries slightly (MRR 0.463 → 0.438): a few ctrl/Erdős candidates displace Mathlib hits.
- The same bias caveat applies as in 6a: I wrote these queries.
- Because of these results, the CLI default is now `auto`: `hybridq` when the Qwen channel is installed, otherwise `hybrid2`. On the PyPI-only path, `auto` is exactly `hybrid2`.
- The MathlibQR benchmark was not rerun with Qwen, because Mathlib has no Qwen vectors and the channel would contribute nothing there.

## 8. Sizes and timings

Main index files (bytes):

| file | size |
|---|---|
| mathdb.sqlite (docs + contentless FTS5) | 272,457,728 |
| char n-gram postings (indptr 16.8 MB, indices 177.8 MB, idf 8.4 MB, norm 1.2 MB) | 204,193,180 |
| emb_wordllama.npy (302,429 × 256 float32) | 309,687,424 |
| records.jsonl.gz | 19,988,625 |
| src.npy + dep.npy | 0.6 MB |
| emb_qwen3.npy + ids/json (optional; 3,543 × 1024) | 14.7 MB |
| **total on disk** | ≈ 784 MB (`du`) |

Compressed sizes:
- The lexical-only set (sqlite + char + records + meta) is 154 MB as tar.gz -6.
- The WordLlama matrix alone is 284 MB gzipped, because floats barely compress.

Build time: 380 s on 4 vCPU, with peak RSS about 2.4 GB.

| step | seconds |
|---|---|
| parse Mathlib | 53 |
| sqlite + FTS5 | 70 |
| char postings | 88 |
| WordLlama | 146 |
| the rest | ≈23 |

Query latency, warm (median / p95, 112-query run, measured while the Qwen job used 3 of 4 cores):

| retriever | median ms | p95 ms |
|---|---|---|
| bm25 | 178 | 524 |
| char | 24 | 44 |
| WordLlama dense | 44 | 57 |
| hybrid2 | 201 | 586 |
| hybrid | 207 | 614 |

- On MathlibQR (`--source mathlib`), hybrid2 had a median of 172 ms.
- Cold CLI calls (system python3, hybrid2) take 0.37-0.59 s. With `--mode hybrid` under the venv it takes 1.2 s, mostly WordLlama load.
- BM25 latency is dominated by FTS5 scoring of OR-queries over common tokens.

## 9. What would improve it (in expected-impact order)

1. **A real embedding model over all of Mathlib.** Section 7 shows that Qwen3-Embedding beats lexical retrieval on paraphrased queries. Candidates are Qwen3-Embedding itself or a math-tuned retriever such as the ones used by LeanSearch, lean-finder or LeanExplore.
   - On this CPU it is infeasible: ≈1.25 s per passage.
   - On one GPU it is roughly an hour.
   - The store already supports drop-in vectors keyed by record id (`emb_qwen3.npy` + `emb_qwen3_ids.json`), so a GPU-built matrix can be shipped as a release asset without touching the code.
   - If Hugging Face access were enabled, sentence-transformers/fastembed models would also become an option.
2. **Informalization.** LeanSearch's approach is an LLM-written natural-language description per declaration. 72% of Mathlib declarations have no docstring, which is why the held-out docstring task tops out at R@10 = 0.45. Even short generated descriptions for theorems would help NL queries.
3. **Generate `@[to_additive]` auto-names** (≈15k) with Mathlib's translation dictionary, and **`@[simps]` projections**. Either use a Lean toolchain (`#print` or doc-gen4 JSON, which would make the parser exact) or port the name-translation table.
4. A **learned or tuned fusion**, e.g. weighted RRF or a small cross-encoder reranker, once a dense channel is worth fusing. WordLlama is not.
5. Smaller wins:
   - BM25 field weights per source;
   - stemming exceptions ("infinitely" vs "infinitude");
   - more synonyms (e.g. "Basel problem" → `hasSum_zeta_two`, "determinant of product" → `det_mul`, both missed).

## 10. Recommended way to ship

- **Code:** keep it in `ctrl/tools/mathdb/`. It is about 2 kLOC of Python, stdlib + numpy for the default path, and does not need its own repo.
- **Index:** a GitHub release asset or similar artifact store, not git.
  - The lexical-only bundle (`mathdb.sqlite`, `char_*.npy`, `src/dep.npy`, `records.jsonl.gz`, `meta.json`) is 154 MB gzipped.
  - Build it in CI from pinned corpus revisions (`meta.json` records them) on a schedule that follows Mathlib.
  - Leave WordLlama out of the default bundle, since it brings no measured benefit and adds 284 MB compressed.
  - Ship Qwen or other dense vectors as a separate optional asset, keyed by record id. The ctrl and Erdős Qwen vectors (14.5 MB) are worth shipping now. Full-Mathlib Qwen vectors (≈300k × 1024 float16 ≈ 600 MB, or int8 ≈ 300 MB) should be built on a GPU.
  - The GGUF itself (639 MB; its license was not verified here) would be a separate download for users who want `hybridq`.
- **Agent access:** wrap `MathDB.search` and `fetch` in a small stdio MCP server, about 60 lines, with tools `math_search(query, k, source, mode)` and `math_get(id)`. Then agents get JSON results without shelling out. `query.py --json` already gives the same payload for CLI use. Neither the MCP server nor the CI job was built or tested here.
- **Complements:** keep `ctrl search` (Loogle, online, type-directed) for exact type queries. mathdb covers offline name, docstring and NL lookup and the non-Mathlib corpora (ctrl, FC, Erdős, OpenAI).

## 11. What I could not verify / caveats

- There is no Lean toolchain, so parser "accuracy" is measured against grep, fc.json, LeanSearch gold names and 60 manual spot checks, not against Lean's environment. Anonymous-instance names are heuristic.
- LeanSearch v2's published 0.623 / 0.533 figures were relayed by the coordinator. I did not see the paper. I also did not check that our protocol matches theirs exactly. I used all 6 query styles, nonempty only, one gold per query, Mathlib only.
- Latency numbers were taken on a shared box with a concurrent 3-thread embedding job, so they are pessimistic.
- The eval indices were rebuilt once after parser fixes. The holdout ids were generated from the first build, and all 40 were found and applied in the rebuilt eval index.
