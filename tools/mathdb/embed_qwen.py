#!/usr/bin/env python3
"""OPTIONAL dense channel: Qwen3-Embedding-0.6B (GGUF, via llama-cpp-python) for a subset of rows.

The default mathdb path never needs this.  It exists because no PyPI wheel ships a
strong embedding model and Hugging Face is blocked here; the GGUF was fetched from
Docker Hub's `ai/` namespace (see README).  CPU throughput on the 4-vCPU build box
was ~70 tokens/s with 3 threads, so only the small corpora are embedded by default.

    python tools/mathdb/embed_qwen.py --index DIR --gguf Qwen3-Embedding-0.6B-Q8_0.gguf \
        [--sources ctrl,erdos] [--threads 3]

Writes into DIR:
  emb_qwen3.npy       (M, 1024) float32, L2-normalised passage vectors
  emb_qwen3_ids.json  record id (docs.id) of each vector -- the join key; rows are re-derived at query
                      time so vectors survive index rebuilds and can be produced elsewhere
  emb_qwen3_rows.npy  (M,) int32 docs.rowid at embedding time (informational)
  emb_qwen3.json      model file name, sources, timing, text recipe
Vectors computed elsewhere (e.g. all of Mathlib on a GPU) can be dropped in with the
same three files, provided rows refer to the same index build (same records.jsonl.gz).
Resumable: progress is kept in emb_qwen3.partial.npz, keyed by record id.
"""
from __future__ import annotations

import argparse
import json
import sqlite3
import sys
import time
from pathlib import Path

import numpy as np

QUERY_INSTRUCT = "Instruct: Given a math search query, retrieve Lean declarations or problem statements that match\nQuery: "


def passage_text(name, statement, doc):
    short = name.split(".")[-1] if not name.startswith("Erdős") else name
    return f"{short}: {(doc or '')[:320]} {(statement or '')[:200]}".strip()


def load_model(gguf: str, threads: int):
    from llama_cpp import Llama
    return Llama(model_path=gguf, embedding=True, n_ctx=1024, n_batch=1024, n_ubatch=1024,
                 n_threads=threads, pooling_type=3, verbose=False)  # 3 = last-token pooling


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--index", type=Path, required=True)
    ap.add_argument("--gguf", required=True)
    ap.add_argument("--sources", default="ctrl,erdos")
    ap.add_argument("--kinds", default="theorem,lemma,erdos_problem",
                    help="record kinds to embed (default: statements only, no defs/modules)")
    ap.add_argument("--threads", type=int, default=3)
    ap.add_argument("--batch", type=int, default=8)
    ap.add_argument("--cache", type=Path, help="npz {ids, E} of vectors already computed (keyed by record id); "
                                               "default <index>/emb_qwen3.partial.npz")
    args = ap.parse_args(argv)
    con = sqlite3.connect(args.index / "mathdb.sqlite")
    srcs = args.sources.split(",")
    kinds = args.kinds.split(",")
    q = (f"SELECT rowid, name, statement, doc, id FROM docs WHERE source IN ({','.join('?' * len(srcs))})"
         f" AND kind IN ({','.join('?' * len(kinds))}) AND deprecated=0 ORDER BY rowid")
    rows = con.execute(q, srcs + kinds).fetchall()
    ids = [r[4] for r in rows]
    texts = {r[4]: passage_text(r[1], r[2], r[3]) for r in rows}
    part = args.index / "emb_qwen3.partial.npz"
    cache = {}
    for f in [args.cache, part]:
        if f and Path(f).exists():
            z = np.load(f)
            cache.update(zip([str(x) for x in z["ids"]], z["E"]))
    todo = [d for d in ids if d not in cache]
    print(f"{len(ids)} passages, {len(ids) - len(todo)} cached, {len(todo)} to embed", file=sys.stderr)
    t0 = time.time()
    ntok = 0
    if todo:
        m = load_model(args.gguf, args.threads)
        for i in range(0, len(todo), args.batch):
            batch = todo[i:i + args.batch]
            bt = [texts[d] for d in batch]
            ntok += sum(len(m.tokenize(b.encode())) for b in bt)
            for d, v in zip(batch, m.embed(bt)):
                cache[d] = np.asarray(v, dtype=np.float32)
            if (i // args.batch) % 25 == 0 or i + args.batch >= len(todo):
                keys = [d for d in ids if d in cache]
                np.savez(part, ids=np.array(keys), E=np.array([cache[d] for d in keys], dtype=np.float32))
                el = time.time() - t0
                print(f"{i + len(batch)}/{len(todo)}  {el:.0f}s  {ntok / max(el, 1e-9):.0f} tok/s",
                      file=sys.stderr, flush=True)
    E = np.array([cache[d] for d in ids], dtype=np.float32)
    E /= np.linalg.norm(E, axis=1, keepdims=True) + 1e-9
    np.save(args.index / "emb_qwen3.npy", E)
    np.save(args.index / "emb_qwen3_rows.npy", np.array([r[0] for r in rows], dtype=np.int32))
    json.dump(ids, open(args.index / "emb_qwen3_ids.json", "w"), ensure_ascii=False)
    json.dump({"model": Path(args.gguf).name, "pooling": "last", "dim": int(E.shape[1]), "sources": srcs,
               "kinds": kinds, "n": int(len(E)), "seconds_this_run": round(time.time() - t0, 1),
               "threads": args.threads, "query_instruct": QUERY_INSTRUCT,
               "passage_recipe": "short name: doc[:320] statement[:200]"},
              open(args.index / "emb_qwen3.json", "w"), indent=1)
    print(f"wrote {E.shape} in {time.time() - t0:.0f}s", file=sys.stderr)


if __name__ == "__main__":
    main()
