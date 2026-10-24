# mathdb: an offline math retrieval index

`mathdb` is a local search index over formal and informal math. It needs no
network, no Lean toolchain and no GPU. Agents and humans query it from the
shell or as JSON.

| source  | what is indexed | license tag |
|---|---|---|
| `mathlib` | every `theorem/lemma/def/abbrev/structure/class/instance/inductive/alias` in `Mathlib/**.lean`, plus one record per module docstring. Each record has its name, signature up to `:=`/`where`, its `/-- -/` docstring, attributes and line | Apache-2.0 |
| `ctrl` | `ControlsLean/**` (working tree) + `lean/**` of `origin/crossover-research-2026-10-19` and `origin/backup/20261020/dev-ctrl/snapshot`. Deduplicated by (name, module), working tree first | MIT (repo LICENSE) |
| `fc` | google-deepmind/formal-conjectures statements with their `category` (research open / research solved / textbook / test / API ...), AMS codes, problem id and `formal_proof` links | Apache-2.0 |
| `erdos` | one record per Erdős problem, merged from `tools/data/erdos.json`, `jsp_erdos_map.json`, plby `data/sources.yaml` and the formal-conjectures main statement | metadata; upstream terms not verified |
| `jsp` | `tools/data/jsp.json` titles, status and Lean links | metadata; upstream terms not verified |
| `openai` | openai/math: family and manuscript titles and abstracts from `CONTENTS.md`, plus up to 40 theorem/proposition/corollary/conjecture environments per manuscript | Apache-2.0 |

## Quick start

```bash
# query (stdlib + numpy are enough; dense part is skipped if wordllama is absent)
export MATHDB_INDEX=/path/to/mathdb-index          # default: ~/.cache/ctrl-mathdb/index
python3 tools/mathdb/query.py "discrete algebraic Riccati equation uniqueness under detectability" -k 10
python3 tools/mathdb/query.py "infinitely many primes" -k 5 --source mathlib
python3 tools/mathdb/query.py "sum-distinct sets 2^n" --source fc,erdos --json
python3 tools/mathdb/query.py Nat.exists_infinite_primes          # exact/suffix name hits come first
```

Options:
- `--mode`: the default is `auto`. It uses `hybridq` when the optional Qwen3
  channel is installed and `hybrid2` otherwise.
  - `hybrid2` is reciprocal-rank fusion of BM25 and char n-grams. It needs
    only the stdlib and numpy and is the best PyPI-only setting.
  - `hybridq` adds Qwen3 vectors for the ctrl and Erdős rows. It was the best
    measured setting overall, especially for ctrl and Erdős queries.
  - The other modes are `hybrid` (adds WordLlama) and the single retrievers
    `bm25`, `char`, `dense` (WordLlama) and `qwen`.
- `--source a,b`
- `--json`
- `--include-deprecated`: deprecated aliases are hidden by default.
- `--full`

Exact or suffix name matches come first, e.g. `Nat.exists_infinite_primes` or
`dare_unique_of_detectable`. So do direct mentions like `Erdős problem 242` and
`JSP-000003`.

## Rebuild

```bash
# 1. environment (exact versions used for the shipped index)
python3 -m venv .venv-mathdb
.venv-mathdb/bin/pip install numpy==2.5.4 PyYAML==6.0.3 wordllama==0.4.0.post1
# (wordllama pulls safetensors 0.8.0, tokenizers 0.23.3, requests; its 256-d
#  "l2_supercat" weights + tokenizer ship INSIDE the wheel, so no Hugging Face access is needed)

# 2. corpora (read-only clones; set MATHDB_CORPORA to their parent dir)
#    mathlib4 (0b57f69), formal-conjectures (c094b97), plby-lean-proofs (8822f7d),
#    openai-math (1581d4c), ctrl-crossover/, ctrl-devsnapshot/ (git archives of the two ctrl branches)

# 3. build (about 10 min on 4 CPUs, peak RSS about 2.4 GB)
.venv-mathdb/bin/python tools/mathdb/build.py --out "$MATHDB_INDEX"
#    --no-dense                     skip WordLlama (index then works with bm25/char/hybrid2 only)
#    --sources mathlib,ctrl,...     subset of sources

# 4. evaluate (add --retrievers bm25,char,dense,hybrid2,hybrid,qwen,hybridq if the Qwen channel is built;
#    the eval index has the held-out Mathlib docstrings removed)
.venv-mathdb/bin/python tools/mathdb/eval.py make-queries --index "$MATHDB_INDEX"   # optional: tools/mathdb/eval/queries.jsonl already exists
.venv-mathdb/bin/python tools/mathdb/build.py --out "$MATHDB_INDEX-eval" --holdout tools/mathdb/eval/holdout_ids.txt
.venv-mathdb/bin/python tools/mathdb/eval.py run --index "$MATHDB_INDEX-eval" --json eval.json

# 5. external benchmark: LeanSearch-v2 MathlibQR (Apache-2.0, github.com/frenzymath/LeanSearch-v2, benchmark/MathlibQR.json)
.venv-mathdb/bin/python tools/mathdb/eval.py leansearch --index "$MATHDB_INDEX" --benchmark /path/to/MathlibQR.json
```

Tested with Python 3.13.16 and SQLite 3.45.1, which has FTS5 compiled in.

## Optional dense channel: Qwen3-Embedding-0.6B (GGUF)

This channel is not needed for the default path. No PyPI wheel ships a strong
embedding model, and huggingface.co is blocked from the build box. The GGUF
`Qwen3-Embedding-0.6B-Q8_0.gguf` was instead pulled from Docker Hub's official
`ai/` namespace by an OCI fetcher (scout lane, `mathdb-scout/bench/fetch_oci.py`).
It runs through `llama-cpp-python`, built from source in a separate venv.

CPU embedding throughput on the 4-vCPU box was about 70 tokens/s with 3
threads uncontended, and about 30-40 tokens/s while other jobs ran. That is
about 1.3 s per passage, so only the small corpora are embedded: ctrl theorems
and lemmas plus the Erdős records, 3,543 passages.

```bash
VENV_LLAMA/bin/python tools/mathdb/embed_qwen.py --index "$MATHDB_INDEX" --gguf Qwen3-Embedding-0.6B-Q8_0.gguf \
    [--sources ctrl,erdos] [--kinds theorem,lemma,erdos_problem] [--threads 3]
export MATHDB_QWEN_GGUF=/path/Qwen3-Embedding-0.6B-Q8_0.gguf
VENV_LLAMA/bin/python tools/mathdb/query.py "..." --mode hybridq     # query embedding uses n_threads=1
```

The vectors are stored as:
- `emb_qwen3.npy` (M x 1024, float32, unit norm);
- `emb_qwen3_ids.json`, the record ids. The query side joins on these ids,
  not on rowids.
- `emb_qwen3.json` (model and recipe).

Because the join is on record ids, vectors for all of Mathlib can be computed
elsewhere and dropped in, for example on a GPU and shipped as a release asset.
Use the passage recipe in `embed_qwen.passage_text` and the same record ids.

## Index layout (`$MATHDB_INDEX/`)

| file | content |
|---|---|
| `mathdb.sqlite` | `docs` table (id, source, kind, name, module, path, line, statement, doc, url, license, deprecated, extra JSON) and a contentless FTS5 table `fts(name, body, src)` using the `porter unicode61` tokenizer over pre-tokenized text |
| `char_indptr.npy`, `char_indices.npy`, `char_idf.npy`, `char_norm.npy` | inverted index of hashed word-boundary char 3-5-grams (2^21 buckets, grams in >20% of docs dropped). Scored with TF-IDF cosine |
| `emb_wordllama.npy` | (N, 256) float32 unit vectors from WordLlama `l2_supercat_256` |
| `emb_qwen3*.{npy,json}` | optional Qwen3 vectors for a subset of rows (see below) |
| `src.npy`, `dep.npy` | per-row source code and deprecated flag, used for fast filtering |
| `records.jsonl.gz` | portable dump of every record |
| `meta.json` | corpus revisions, counts, build timings, file sizes, package versions |

Tokenization (`common.tokenize`):
- splits `camelCase`, `snake_case` and dotted names, and also keeps the joined
  compound (`natexistsinfiniteprimes`);
- turns LaTeX commands into words;
- encodes unicode math symbols as `u<hex>` tokens and adds an English gloss
  (`∑` → `sum`, `ℝ` → `real`, `∣` → `dvd divides`, ...);
- names also get glosses for Lean and controls abbreviations (`dvd`, `deriv`,
  `dare`, `lqr`, ...).

## Parser notes and known gaps

`lean_parse.py` is a comment/string-aware regex parser. It strips nested
`/- -/` comments, tracks `namespace/section/end/mutual`, splits
`alias ⟨a, b⟩ := foo_iff` into two records, and emits the extra name for
`@[to_additive explicitName]`. Things it does not cover:
- Names auto-generated by `@[to_additive]` without an explicit name (about
  15k Mathlib declarations).
- Names from `@[simps]`, `deriving` and structure projections.
- Declarations made by macros (`irreducible_def`, `notation`, ...).
- Anonymous instances get an approximate `inst...` name, flagged in `extra.anonymous_instance`.
- `variable` binders are not added to signatures.

Measured parser accuracy and retriever comparisons are in the wave-2 report
`MATHDB-BUILD.md`.
