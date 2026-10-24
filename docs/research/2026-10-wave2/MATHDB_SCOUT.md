# MATHDB-SCOUT: how to build a best-in-class math retrieval DB for ctrl

Lane: MATHDB-SCOUT. Date: 2026-10-24. Author: research subagent (no index built; only a throughput benchmark run).
Scratch evidence: `(session scratch directory, not committed)/`
(cloned repos under `repos/`, benchmark under `bench/`).

## 0. Five findings that change the plan

1. **Strong embedding models are reachable today through Docker Hub.** The proxy allows
   `registry-1.docker.io`, `auth.docker.io` and `production.cloudfront.docker.com`. Docker's `ai/` namespace
   publishes OCI "model artifacts" whose layers are the raw files. Each layer carries an
   `org.cncf.model.filepath` annotation, so a 30-line stdlib script (`bench/fetch_oci.py`) rebuilds the HF directory.
   Verified downloads: `ai/qwen3-embedding:0.6b-q8_0` (639 MB GGUF, fetched in under a minute) and a ranged read
   of `ai/qwen3-embedding:0.6b-safetensors` (manifest annotation `ai.model.repo: Qwen/Qwen3-Embedding-0.6B`, full
   sentence-transformers layout including `1_Pooling/config.json`, `model.safetensors` 1.19 GB).
   Also present: `qwen3-embedding` 4B and 8B (safetensors + GGUF), `qwen3-reranker` 0.6B/4B/8B (GGUF),
   `qwen3-reranker-vllm`, `qwen3-embedding-vllm`, `embeddinggemma`, `nomic-embed-text-v1.5`,
   `nomic-embed-text-v2-moe(-safetensors)`, `mxbai-embed-large`, `snowflake-arctic-embed-l-v2-vllm`,
   `granite-embedding-multilingual`, `all-minilm-l6-v2-vllm`.
   **So the best general open embedder used by every 2026 math-search system (the Qwen3-Embedding family)
   needs no allowlist change.**
2. **GitHub release assets and Git LFS media are downloadable** (`curl -L` on `github.com/.../releases/download/...`
   gives HTTP 206 from `release-assets.githubusercontent.com`; `media.githubusercontent.com` returns 200).
   CONTEXT.md says "github.com release HTML" is blocked. That is true for HTML pages only, not for assets.
   Consequence: **elan and Lean toolchains (including `v4.36.0-rc1`, ctrl's pin, and `v4.34.1`, openai/math's pin)
   install from GitHub releases.** The Mathlib build cache (`cache.mathlib.org`, lakecache blob) stays blocked, so
   elaborated extraction (doc-gen4 / jixia / LeanGraph / Loogle) needs a from-source Mathlib build. I estimate several
   CPU-hours on 4 cores; I did not run it.
3. **Ready-made eval sets ship in GitHub repos (Apache-2.0)**, so the baseline index can be scored today with no HF access:
   * `frenzymath/LeanSearch-v2/benchmark/MathlibQR.json`: 200 Mathlib declarations with gold `full_name`, up to 6 query
     styles each (Lean-ish, LaTeX, natural, slogan, nickname, special case); 946 rows in total, plus
     `MathlibQR_shared171.json` (the 810-row "fair" subset used by LeanSearch v2, Lean Finder V2 and TheoremGraph).
     `MathlibMPR.json` holds 69 theorems with premise-group ground truth. `FATE-H.jsonl` is CC BY 4.0.
   * `delta-lab-ai/lean-finder/lean-finder-original/data/test/*.jsonl`: 7,448 queries with positive passages, in five
     files: 1,000 synthetic user queries, 1,000 informalized statements, 1,000 augmented statements, 2,224 raw proof
     states and 2,224 augmented proof states.
   These are the published numbers to compare against, so **use MathlibQR as ctrl's headline metric**.
4. **Every prebuilt Mathlib index is hosted on Hugging Face or Cloudflare R2, and both are blocked.** That covers the
   LeanSearch v2 corpus/cuVS index, the Lean Finder corpora and FAISS indices, the Herald/LeanSearch informal dataset,
   the LeanPremise/LeanHammer premise corpus, the TheoremSearch dataset and the MIRB data (all HF), plus the
   LeanExplore DB (R2, `pub-48b75babc4664808b15520033423c765.r2.dev`). The code to rebuild each one is on GitHub.
   The most valuable missing piece is not the vectors but the **LLM informalizations**: each project paid an LLM to
   write natural-language descriptions of about 200–250k declarations.
5. **openai/math is larger than it looks.** It has 749 preprint dirs (746 with LaTeX sources; README: "719 manuscripts in
   372 families", with 3 withdrawn on 2026-10-07). It contains about 22.6k theorem-like LaTeX environments
   (13,603 lemma / 5,221 proposition / 2,431 theorem / 1,380 corollary / 598 definition). The Lean side has 122,458 files
   and 26.1M lines, with about 2.21M `theorem|lemma` lines. There are 416 Comparator challenge JSONs naming 537 top-line
   theorem declarations, and `formalization.yaml` maps each one to its paper. That gives about 300 verified
   **informal↔formal pairs** ("~42% of top-line results formalized"). License Apache-2.0. Pinned to Lean v4.34.1, with
   Mathlib rev `d13f23b7`.

Reusable artifacts: `mathdb-scout/bench/fetch_oci.py` (stdlib Docker Hub model fetcher), `mathdb-scout/bench/q3e-q8/Qwen3-Embedding-0.6B-Q8_0.gguf` (639 MB, already downloaded), `mathdb-scout/bench/venv` (built llama-cpp-python 0.3.36), `mathdb-scout/repos/` (all cloned systems + benchmarks).

Two notes on the container itself. First, an elan toolchain `leanprover--lean4---v4.36.0-rc1` now exists under `/root/.elan`,
apparently installed by another lane, which contradicts CONTEXT.md's "no Lean". `ctrl/.lake` holds no built Mathlib.
Second, the machine was heavily contended during this lane (load average 12–32 on 4 vCPUs), which affects the benchmark in §3.4.

---

## 1. Prebuilt math search and retrieval systems

"Reachable" means reachable from this container (GitHub git/raw/releases, PyPI, npm and Docker Hub work; huggingface.co,
arxiv.org, R2 and most other hosts do not, and WebFetch also fails on arxiv, alphaxiv and emergentmind).

| System | What it is | Data / index | Freshness | License | Reachable here? |
|---|---|---|---|---|---|
| **LeanSearch v2** (`frenzymath/LeanSearch-v2`, May 2026, last commit 2026-05-18) | jixia extraction → dependency-aware ("hierarchy") LLM informalization → Qwen3-Embedding-8B + Qwen3-Reranker-8B (the public leansearch.net uses a 4B reranker); a reasoning mode for global premise retrieval | HF `FrenzyMath/lsv2-mathlib-v4.28.0-rc1-jsonl` (records) and `...-cuvs` (vectors) | Mathlib v4.28.0-rc1 | Apache-2.0 code; dataset license not checked (HF blocked) | **Code and benchmarks: yes (git). Data: no (HF).** API leansearch.net: no |
| **LeanSearch v1** (`frenzymath/LeanSearch`, 2024; last commit 2026-01-23) | jixia → Postgres → DeepSeek informalization → e5-mistral-7b + Chroma | HF `FrenzyMath/mathlib_informal_v4.16.0` (the Herald-style informal dataset; Lean Finder also cites `..._v4.19.0`) | v4.16 / v4.19 | Apache-2.0 code | Code yes, data no |
| **Lean Finder** (`delta-lab-ai/lean-finder`, ICLR 2026; repo updated 2026-05-21) | Embedder fine-tuned on synthesized user-intent queries (Tevatron, LoRA); GPU ≥16 GB for the 7B-class model; "newly updated" model on HF `main` | HF model repo `delta-lab-ai/lean-finder` holds the corpora `mathlib4_{19,24,28}_0.jsonl` and FAISS indices | v4.19.0 / v4.24.0 / v4.28.0 | Apache-2.0 | Code + **7,448 test queries in git: yes**. Model/corpus: no. **Lean Finder V2** (arXiv 2610.30843, submitted 2026-10-22) claims +14% relative Recall@10 on MathlibQR over the previous best; release status unverified |
| **LeanExplore** (`justincasher/lean-explore`, PyPI `lean-explore` 1.3.0, 2026-08-02; repo 2026-09-28) | doc-gen4-based extraction; informalization with `google/gemini-3-flash-preview` via OpenRouter; BM25 on names (two tokenizations) + FAISS over informalizations (Qwen3-Embedding-0.6B) + RRF + dependency boost + Qwen3-Reranker-0.6B; MCP server and Claude Code plugin | `lean-explore data fetch` from Cloudflare R2 (`pub-48b7…r2.dev/assets/latest.txt`) | Packages: Batteries, CSLib, FLT, **FormalConjectures**, Init, Lean, Mathlib, PhysLean, Std. Default cache version string `v4.24.0` (docs) | Apache-2.0 code; data license not stated | Code/PyPI yes; **data no (R2 blocked)**; hosted API (30 req/min/IP) no |
| **TheoremSearch** (`uw-math-ai/TheoremSearch`, NeurIPS 2026 D&B; repo 2026-10-02) | 9.2M informal theorem statements (arXiv + Stacks + 6 other sources), Qwen3-235B slogans, Qwen3-Embedding-8B; REST + MCP (`theorem_search`) | HF `uw-math-ai/theorem-search-dataset` | rolling | paper CC BY-SA 4.0; dataset license not checked | Code + ingestors (ProofWiki, nLab, Stacks, OEIS, DLMF, FindStat, PDF) yes; data and API no |
| **TheoremGraph / LeanGraph** (arXiv 2606.25363, same group) | 388,105 Lean declaration nodes / 11.3M typed edges over 25 projects; 47,952 judge-accepted informal↔formal matches; extractor `aurasoph/lean-graph`; corpus_v3 SQLite (Mathlib v4.27–v4.29 + 24 projects incl. FLT, PFR, Carleson, PNT+, formal-conjectures) | corpus DB location not verified (README in `formalized_graph_v2/corpus_v3`) | v4.27–v4.29 | — | README/scripts yes; DB not located |
| **LeanPremise / LeanHammer premise server** (`hanwenzhu/premise-selection`, `hanwenzhu/lean-premise-server`; updated Aug–Oct 2026) | encoder-only retriever over goal states; Lean-side `Lean.LibrarySuggestions.Cloud.premiseSelector` with combinators to the **built-in MePo / sineQuaNon selectors** | HF `l3lab/lean-premises` + model via TEI | tagged Mathlib releases | Apache-2.0 | Code yes; data/model no; leanpremise.net not tested |
| **LeanStateSearch** (premise-search.com) | goal-state → theorem search, used by `#search` in LeanSearchClient | hosted | — | — | No (proxy rejects premise-search.com). Source repo not found |
| **Loogle** (`nomeata/loogle`, 2026-07-09) | type/pattern search; needs Lean + Mathlib built (`lake build LoogleMathlibCache`) | built locally | matches your build | Apache-2.0 | Buildable once Mathlib is built from source (no cache) |
| **Moogle** | NL search (`#moogle` in LeanSearchClient) | hosted | — | — | No; status unverified, likely superseded |
| **LeanDojo v2** (`lean-dojo/LeanDojo-v2`, PyPI `lean-dojo-v2` 1.0.9) | tracing + `RetrievalTrainer` / `RetrievalProver` (ReProver lineage); no shipped prebuilt index | tracing needs Lean + built repo | — | Apache-2.0 repo / MIT PyPI | Code yes |
| **lean-lsp-mcp** (PyPI 0.31.0, 2026-09-30, MIT) | MCP wrapper: `lean_leansearch`, `lean_loogle`, `lean_leanfinder` (via `lean-lsp-proxy.leanfinder.workers.dev`), `lean_hammer_premise`, `lean_local_search` (ripgrep over the project + deps), plus LSP tools (`lean_goal`, `lean_hover_info`, `lean_multi_attempt`, `lean_verify`, ...) | remote backends; `LOOGLE_URL`, `LEAN_LOOGLE_LOCAL` etc. for self-hosting | — | MIT | Installs from PyPI; remote search backends blocked; `lean_local_search` works offline |
| **doc-gen4 declaration data** | `declarations/declaration-data.bmp` (JSON) emitted by doc-gen4 | `leanprover-community/mathlib4_docs` has **no gh-pages branch**; docs deploy via Pages artifacts | — | Apache-2.0 | Not fetchable; must run doc-gen4 yourself (needs built Mathlib) |
| **MIRB** (`j991222/mirb`) | 12-dataset math IR benchmark incl. LeanDojo premise retrieval (4,109 proof-state queries over 180,944 Mathlib4 decls) and NaturalProofs | HF collection `hcju/mirb` | — | — | Code yes, data no |
| Kimina / Goedel-Prover-V2 | No retrieval component found. "Gödel's Poetry" (2512.14252) adds RAG to a Goedel-V2 pipeline | — | — | — | n/a |

**Benchmark numbers I saw** (from search-result summaries of the papers; I could not open the PDFs because arxiv is blocked):
* LeanSearch v2 standard mode reaches **nDCG@10 0.623 on MathlibQR vs 0.533** for the next-best system, with no domain
  fine-tuning. Reasoning mode recovers **46.1%** of premise groups at 10 candidates on MathlibMPR. Prover loop: 20% vs 16%
  for the next-best retriever, and 4% with no retrieval.
* TheoremGraph reaches **Recall@10 0.775 on MathlibQR fair-810 without a reranker**, vs LeanSearch v2 reranked 0.780. The
  paper attributes the differences to *what text is embedded per passage*, with the embedder held fixed (Qwen3-Embedding-8B).
* Lean Finder V2 reports +14% relative Recall@10 on MathlibQR. A garbled table excerpt lists LeanExplore at nDCG@10 ≈ 0.406
  on the 810 set (low confidence).
* TheoremSearch (README) reports theorem-level Hit@10 **0.432**, vs Gemini 3 Pro 0.252 and ChatGPT 5.2 0.180.
  Paper-level: 0.505 vs Google 0.378.
* MIRB, LeanDojo premise task (third-party SOTA2 leaderboard, unverified against the paper): nDCG@10 Octen-Embedding-8B 14.3,
  Qwen3-Embedding-8B 13.6, Qwen3-Embedding-4B 13.2, harrier-oss-v1-0.6B 8.7. **Proof-state → premise retrieval with
  general embedders is weak.** That is the job of dedicated premise selectors (LeanPremise, ReProver), not a semantic DB.

**Takeaway.** Every 2026 state-of-the-art system shares one recipe:
(a) elaborated extraction (jixia / doc-gen4 / LeanGraph) with full names, pretty-printed types and dependency edges;
(b) **LLM informalization done bottom-up over the dependency DAG**;
(c) a Qwen3-Embedding model (0.6B for LeanExplore, 8B for LSv2 and TheoremSearch);
(d) BM25 on names, fused with dense retrieval;
(e) optionally a Qwen3 reranker.
The measured gains come from (a), (b) and the embedder size, not from exotic indexing.

## 2. Informal-math corpora

| Corpus | Size (what I measured or saw) | License | Reachable here | Notes |
|---|---|---|---|---|
| **openai/math** (`$C/openai-math`, HEAD 1581d4c, 2026-10-12) | 749 preprint dirs / 746 with LaTeX (`build/source/*.tex`, 135 MB of .tex); 719 manuscripts / 372 families (README); ≈22.6k theorem-like environments; Lean: 122,458 files, 26.1M lines, ≈2.21M theorem/lemma lines; 416 Comparator JSONs → 537 top-line theorem names; `formalization.yaml` v0.4 (`status.main_results`) | Apache-2.0 | yes (already cloned) | Best informal↔formal pairing source available. Mind the 3 withdrawals and 14 revisions (`history.md`). Index only the *top-line* Lean decls plus the LaTeX statements, not all 2.2M auxiliary lemmas |
| **Stacks Project** (`stacks/stacks-project`) | `tags/tags` lists 21,583 tags (sections, lemmas, equations); TheoremSearch repo ships 244 slogans in `data/stacks_slogans.csv` | GFDL 1.2 (`COPYING`) | **yes (git)** | Stable tags make good record IDs |
| **nLab** (`ncatlab/nlab-content`, plus `nlab-content-html`) | 41,556 tree entries ≈ 20.8k pages (`pages/**/content.md` + `name`) | **No formal license.** The homepage asks for attribution; an nForum thread confirms contributors never agreed to a license (some, e.g. Urs Schreiber, state CC BY-SA 3.0 for their own edits) | **yes (git)** | Fine for a private local index; do not redistribute |
| **OEIS** (`oeis/oeisdata`) | full export, `time.txt` = 2026-10-24T03:00 | CC BY-SA 4.0 | **yes (git)** | Useful for combinatorics / number theory lanes (Erdős) |
| **HoTT book** (`HoTT/book`) | one book | CC BY-SA | yes (git) | small |
| **ProofWiki** | no official dump found; MediaWiki API only | CC BY-SA 3.0 (ToS) | **no** (proxy) | NaturalProofs' `proofwiki.json` (CC BY-SA 4.0) is on Zenodo (blocked); `wellecks/naturalproofs` repo not checked |
| **Kerodon** | — | not found | no (kerodon.net blocked; no public source repo found) | skip |
| **Math.SE / MathOverflow** | dumps moved behind login in 2024, with terms barring LLM training | CC BY-SA 4.0 content | no (archive.org blocked) | skip |
| **OpenWebMath / Proof-Pile-2** (55B tokens: arXiv 29B, OWM 15B, AlgebraicStack 11B) | ≈48 GB zip (mirror figure) | mixed / per-source | no (HF only) | Pretraining scale; wrong tool for a curated DB |
| **MathPile** | ≈9.5B tokens (not verified) | CC BY-NC-SA (not verified) | no (HF) | skip |
| **arXiv bulk** | — | per-paper | no (arxiv, S3 requester-pays) | Use TheoremSearch's 9.2M extracted statements instead if HF opens |

## 3. Embedding models (2026)

### 3.1 What the strongest systems use
* **Qwen3-Embedding-8B** (Apache-2.0, 4096-d, 32K context; MTEB-multilingual #1 at 70.58 in June 2025 per secondary
  sources): used by LeanSearch v2, TheoremSearch and TheoremGraph.
* **Qwen3-Embedding-0.6B** (Apache-2.0, 1024-d, MMTEB mean 64.33 per a secondary source): used by LeanExplore, with
  **Qwen3-Reranker-0.6B**.
* **Lean Finder** model (Apache-2.0; GPU ≥16 GB): the only *Lean-specialized* semantic embedder with public weights. HF only.
* **Premise selectors** (LeanPremise encoder, ReProver ByT5): trained on goal-state → premise pairs; HF only.
* Other options: EmbeddingGemma-300M (Gemma Terms of Use, not OSI), nomic-embed v1.5 / v2-moe, mxbai-embed-large, arctic-embed-l-v2.
  A vendor blog claims zembed-1 leads "STEM/math" NDCG@10 (0.528 vs voyage-4-nano 0.501); that is an API model, and the
  claim is the vendor's own.

### 3.2 Where each one can be obtained here
| Model | Docker Hub (`ai/…`) | PyPI | GitHub | HF |
|---|---|---|---|---|
| Qwen3-Embedding-0.6B / 4B / 8B | **yes**: `ai/qwen3-embedding:{0.6b,4b,8b}-safetensors`, GGUF `-q8_0`, `-f16`, `-q4_K_M` | no | no | blocked |
| Qwen3-Reranker-0.6B / 4B / 8B | **yes**: `ai/qwen3-reranker:{0.6B,4B,8B}` (GGUF); `ai/qwen3-reranker-vllm` (safetensors, not inspected) | no | no | blocked |
| EmbeddingGemma-300M | yes: `ai/embeddinggemma:{bf16,q8_0,q4_0}` GGUF (from `unsloth/embeddinggemma-300m-GGUF`) | no | no | blocked |
| nomic-embed-text v1.5 / v2-moe, mxbai-embed-large, arctic-l-v2, granite-multilingual, all-MiniLM-L6-v2 | yes | no | no | blocked |
| WordLlama (static, tiny) | — | **yes** (weights inside the 19 MB wheel) | — | — |
| Lean Finder, LeanPremise, ReProver, model2vec/potion | no | no (model2vec downloads from HF) | no | blocked |

Docker Hub layers are content-addressed (sha256 digests in the manifest), so downloads are verifiable. The model license
travels with the weights: Qwen3 is Apache-2.0; EmbeddingGemma is under Gemma terms.

### 3.3 Runtimes that install from PyPI
* `llama-cpp-python` 0.3.36 (builds from source here in about 15 minutes with the system gcc/cmake; AVX-512 VNNI detected)
  runs the GGUF embedders and rerankers on CPU.
* `sentence-transformers` 6.2.0 runs the safetensors directories, but needs `torch` from PyPI. The Linux wheel there pulls
  the CUDA dependencies (several GB; download.pytorch.org is blocked). It works on CPU but is heavy.
* `onnxruntime` 1.31 needs an ONNX export, and none was found on reachable hosts.
* Stores: `faiss-cpu` 1.15.1, `usearch` 2.26.5, `sqlite-vec` 0.1.9, `lancedb` 0.40, `duckdb` 2.0, `tantivy` 0.27, `bm25s` 0.3.15.
* MCP: `mcp` 2.3.0, `fastmcp` 4.1.3.
* PyPI name collision: `leansearch` 0.1.1 (2026-10-22) is an unrelated full-text/vector library, not FrenzyMath's LeanSearch.

### 3.4 CPU cost, measured (with caveats)
Benchmark: Qwen3-Embedding-0.6B Q8_0 GGUF via llama-cpp-python, on this container while other lanes held load
average 12–32 on 4 vCPUs. Script: `bench/bench.py`.
* Short statements (≈31 tokens): **8–15 tokens per CPU-second**, i.e. 0.24–0.47 statements per CPU-second.
* An 802-token input: 22 tok/s single-threaded and 17 tok/s with 4 threads; the threads were fighting the contention.
* A single short query embedded in **0.44 s single-threaded**. The same query took 16–20 s with 4 threads under contention,
  so use `n_threads=1` for query-time embedding on a shared box.
* For reference, numpy fp32 matmul ran at 68 GFLOPS on one core at the same time. The machine is not slow; llama.cpp
  embedding was badly hit by contention and possibly by per-call overhead.

I could not get an uncontended number. Theory: the 0.6B model costs about 1.2 GFLOP per token. Mathlib has ≈260k
source-level declarations (regex count on HEAD 0b57f69: 129,867 theorem, 61,193 lemma, 33,001 def, 27,694 instance,
3,692 abbrev, 2,065 class, 1,840 structure, 356 inductive). Embedding at ≈60 tokens each is ≈16M tokens ≈ 2×10^16 FLOP:
* **about 1–3 days of exclusive 4-core CPU** for 0.6B;
* about 13× that for 8B, i.e. impractical on CPU.

Query-time embedding with the 8B model on CPU is plausible (seconds per query), but I did not measure it.
**Practical rule: in this container, embed corpora with 0.6B selectively, or embed elsewhere on a GPU and ship the
vectors as a GitHub release asset, which every container can download.**

### 3.5 If exactly one allowlist entry is added
**Add `huggingface.co`.** Its file CDN hosts must come with it (`*.hf.co`, i.e. `cas-bridge.xethub.hf.co` / `cdn-lfs.hf.co`;
HF downloads redirect there). In practice that is one entry, "huggingface.co and its CDN".

Since the models already arrive via Docker Hub, HF mostly buys **data**:
* the LSv2 Mathlib v4.28.0-rc1 corpus, with hierarchy informalizations and precomputed Qwen3-8B vectors (the configuration
  behind nDCG@10 0.623 on MathlibQR, vs ≈0.53 next-best);
* TheoremSearch's 9.2M informal theorem statements and slogans (Hit@10 0.432, vs ≤0.252 for frontier LLMs);
* the Lean Finder model and its corpora (v4.19, v4.24, v4.28);
* the Herald informal dataset, `l3lab/lean-premises`, and the MIRB data.

The key trick: with the LSv2 vectors downloaded, only **queries** need the 8B encoder, which comes from Docker Hub GGUF.
That reproduces LSv2 retriever-only quality locally with no GPU. By contrast, a BM25/TF-IDF baseline over raw Lean source
typically sits well below these dense+informalized systems. I have no MathlibQR number for a pure-BM25 Mathlib index, so
**run the baseline on MathlibQR before quoting a gap.**

The runner-up single entry is `pub-48b75babc4664808b15520033423c765.r2.dev`. It unlocks LeanExplore's complete local DB:
informalizations, FAISS and BM25, already covering FormalConjectures, FLT, CSLib and PhysLean. It is narrower, and its data
license is unstated.

## 4. Serving: how agents should consume it

Recommended: **one Python package, two front-ends over the same store.**
1. **MCP server (stdio)**, the primary interface for agents. Copy LeanExplore's token-efficient pattern: a cheap
   `search_summary` that returns ids, names and one-line descriptions, plus per-field fetch tools. Suggested tools:
   * `search(query, k=10, sources=[mathlib, formal_conjectures, ctrl, openai_math, stacks, nlab, oeis], kind=…, mode=hybrid|lexical|dense)`
   * `get(id, fields=[statement, informal, docstring, source_link, deps])`
   * `related(id)`: dependencies / dependents / informal↔formal matches
   * `by_type(pattern)`: a Loogle-like name/type substring search until real Loogle is available

   Expose records as MCP resources `mathdb://<source>/<id>` so clients can attach them.
   Every result carries `source`, `version` (Mathlib rev), `license` and a `url` (GitHub blob link + line), so agents can
   cite and check.
2. **CLI with `--json`** (e.g. `python -m tools.mathdb.query "…" --json -k 20 --source mathlib`) for scripts, CI, and
   agents without MCP.
3. A static site search adds little for agents. Skip it, or generate a pagefind-style index later for humans.

Existing open-source MCP servers to reuse or imitate:
* **lean-lsp-mcp** (MIT, PyPI 0.31.0): `lean_leansearch`, `lean_loogle`, `lean_leanfinder`, `lean_hammer_premise`,
  `lean_local_search` plus LSP tools. Its backends are overridable by env var (`LOOGLE_URL`, `LEAN_LOOGLE_LOCAL`,
  `LEAN_STATE_SEARCH_URL`, `LEAN_HAMMER_URL`), so a ctrl MathDB could be plugged in behind a compatible HTTP endpoint.
* **lean-explore MCP** (Apache-2.0, PyPI 1.3.0): `search_summary`, `search` (deprecated), `get_source_code`,
  `get_source_link`, `get_docstring`, `get_description`, `get_module`, `get_dependencies`; local backend via
  `lean-explore mcp serve --backend local`.
* **TheoremSearch MCP**: a single tool `theorem_search` at `https://api.theoremsearch.com/mcp` (remote; not reachable here).

## 5. Recommendation for ctrl

### v1: buildable today in this container (no allowlist change)
**Corpora**, with record id = `source:qualified_name_or_tag`:
1. Mathlib at **ctrl's pin** (`v4.36.0-rc1` per `lake-manifest.json`). The shared clone is HEAD 0b57f69, so check that it
   matches the pin or re-clone at the tag. Include docstrings (≈73k `/--` blocks).
2. formal-conjectures (1,954 files, ≈8.2k theorem/lemma lines).
3. ctrl's own `ControlsLean` (+ crossover / RoboLean snapshots).
4. **openai/math**: the 537 top-line Lean theorems from `ComparatorChallenges/*.json`, the ≈22.6k LaTeX theorem/lemma/
   proposition statements (with paper title and family as context), and an explicit `formalizes` edge from
   `formalization.yaml` / the Comparator JSON. Exclude withdrawn papers (`history.md`).
5. Stacks Project (tags as ids, GFDL).
6. nLab pages (local use only, no clear license).
7. OEIS names/comments (CC BY-SA), if the Erdős / combinatorics lanes want it.
8. plby/lean-proofs (563 Erdős proofs) to link problems → proofs.

**Retrieval stack:**
* Keep the other lane's lexical baseline: BM25 over names with Lean-aware tokenization (split dots, `_` and camelCase; map
  symbols to words) and over statement + docstring text.
* Add a dense channel with **Qwen3-Embedding-0.6B from `ai/qwen3-embedding:0.6b-q8_0`** (or the safetensors build if torch
  is acceptable). Given §3.4, embed in priority order: every decl with a docstring, openai/math statements, Stacks, nLab,
  formal-conjectures and ctrl, which is ≈150k short texts. Embed the rest of Mathlib as a background job or off-box.
  WordLlama (bundled in its wheel) stays as the zero-download fallback.
* Fuse with RRF, plus a dependency/name-prefix boost.
* Optionally add `ai/qwen3-reranker:0.6B` (GGUF, llama.cpp) for the top 25 when latency allows.
* **Evaluate on MathlibQR (946 rows; 184/200 gold decls still in the same file at HEAD) and the Lean Finder test files
  before and after every change.** Report Recall@1/5/10, nDCG@10 and MRR, so ctrl's numbers sit next to the published
  0.53–0.62 nDCG@10.

**Store:** SQLite (records, edges, FTS5 or bm25s) plus a flat `float16` numpy / usearch index per (source, model); 1024-d ×
300k rows ≈ 0.6 GB fp16. Ship it as a single directory keyed by Mathlib rev.

**Serving:** the MCP + CLI described in §4.

**Refresh:** rebuild when ctrl's `lean-toolchain` / `lake-manifest.json` Mathlib rev changes (today `v4.36.0-rc1`). Hash
`(qualified_name, statement_text)` and re-embed only changed rows; a typical Mathlib bump touches a few thousand
declarations, which is hours on CPU rather than days. Refresh openai/math on new tags in `history.md`. Refresh Stacks,
nLab and OEIS monthly.

**Build cost, v1:** lexical index takes minutes. Model download takes about 1 minute (0.64 GB GGUF) or about 2 minutes
(1.2 GB safetensors). Dense embedding of the ≈150k priority texts is **roughly 10–30 CPU-hours** on an uncontended 4-vCPU
box. This is my estimate from theory plus the contended measurement, so low confidence; measure before committing.
A full-Mathlib dense pass on CPU is 1–3 days, so do it off-box or pull it from HF in v2.

**Optional v1.5 (still no allowlist change):** build Mathlib from source with the GitHub-release toolchain (several
CPU-hours, unmeasured), then run jixia or doc-gen4 for elaborated names, types and dependency edges, and local Loogle.
Elaborated types and dependency edges are what LSv2 and TheoremGraph show matters most.

### v2: with `huggingface.co` (+ `*.hf.co` CDN) allowlisted
* Import the **LSv2 v4.28.0-rc1 JSONL + Qwen3-8B vectors** for Mathlib. Encode queries with **Qwen3-Embedding-8B GGUF
  from Docker Hub** on CPU.
* Re-embed only the v4.28→v4.36 delta with the same 8B model (a few thousand rows; hours on CPU) so vectors stay in one space.
* Add **TheoremSearch's 9.2M informal statements** as an "informal literature" source, embedded in the same 8B space,
  which enables cross-modal informal↔formal search the way TheoremGraph does.
* Add the **Lean Finder model** as a second dense channel for user-intent queries, if a GPU is ever available; on CPU a
  7B-class encoder is query-time only.
* Add the reranker `ai/qwen3-reranker:4B` or `8B`, which is what the 0.623 number used.
* **Expected quality:** roughly LSv2 retriever-only to LSv2-reranked level on MathlibQR (published nDCG@10 ≈ 0.62,
  Recall@10 ≈ 0.78), versus whatever the v1 baseline measures. The informalizations are the main lever.
* **Build cost:** about 10–40 GB of downloads (the 9.2M-row vector set dominates; unverified); vector store ≈ 9.5M × 4096 ×
  fp16 ≈ 78 GB, which **does not fit in the 25 GB disk**. So keep TheoremSearch text-only + BM25, or PCA/Matryoshka-truncate
  to 512-d (Qwen3 supports MRL), ≈ 9.7 GB fp16. Mathlib from LSv2: ≈ 250k × 4096 fp16 ≈ 2 GB.

### Licensing hygiene
* Mathlib, formal-conjectures, openai/math, LSv2 code and Lean Finder are Apache-2.0.
* Stacks is GFDL. OEIS and ProofWiki are CC BY-SA. nLab is unlicensed: keep it local, never republish.
* EmbeddingGemma is Gemma terms; prefer Qwen3 (Apache-2.0).
* Store `license` per record and refuse to export unlicensed sources.

## What I could not verify
* I could not open any arXiv PDF (arxiv, alphaxiv and emergentmind are blocked for both curl and WebFetch). Every paper
  number above comes from search-engine summaries or GitHub READMEs.
* HF dataset licenses, sizes and exact contents (LSv2, Lean Finder, TheoremSearch, Herald, MIRB). LeanExplore's latest
  data version on R2.
* An uncontended CPU embedding throughput, the 8B query latency, and Mathlib from-source build time.
* Whether `ai/qwen3-reranker-vllm` contains safetensors. Kerodon source availability. The LeanStateSearch source repo.
