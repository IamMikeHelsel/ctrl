#!/usr/bin/env python3
"""Query the offline math index.

    python3 tools/mathdb/query.py "discrete algebraic Riccati equation uniqueness" -k 10
    python3 tools/mathdb/query.py "infinitely many primes" --source mathlib --json
    python3 tools/mathdb/query.py "sum-distinct sets" --source fc --mode bm25

Modes: auto (default: hybridq when the optional Qwen3 channel is installed, else
hybrid2), hybrid2 (reciprocal-rank fusion of BM25 + char n-grams, the best PyPI-only
setting), hybrid (+ WordLlama), hybridq (+ optional Qwen3 channel),
bm25, char, dense (WordLlama), qwen.  Sources: mathlib, ctrl, fc, erdos, jsp, openai.
Needs only python3 + numpy for the default mode; `wordllama` for dense/hybrid;
llama-cpp-python + the Qwen3-Embedding GGUF for qwen/hybridq.
Index location: --index or $MATHDB_INDEX (default: ~/.cache/ctrl-mathdb/index).
"""
from __future__ import annotations

import argparse
import json
import re
import sqlite3
import sys
import time
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common as cm  # noqa: E402

SOURCES = ("mathlib", "ctrl", "fc", "erdos", "jsp", "openai")


class MathDB:
    def __init__(self, index: Path = cm.DEFAULT_INDEX, dense: bool = True, qwen_gguf: str | None = None):
        self.index = Path(index)
        db = self.index / "mathdb.sqlite"
        if not db.exists():
            raise SystemExit(f"index not found: {db}  (build it with tools/mathdb/build.py)")
        self.con = sqlite3.connect(f"file:{db}?mode=ro", uri=True)
        self.N = self.con.execute("SELECT count(*) FROM docs").fetchone()[0]
        self._src = None
        self._dep = None
        self._char = None
        self._emb = None
        self._wl = None
        self.dense_ok = dense and (self.index / "emb_wordllama.npy").exists()
        self._qwen = None
        self.qwen_gguf = qwen_gguf

    # ---- lazily loaded arrays ------------------------------------------
    def src_codes(self):
        if self._src is None and (self.index / "src.npy").exists():
            self._src = np.load(self.index / "src.npy")
            self._dep = np.load(self.index / "dep.npy")
        if self._src is None:
            src = np.zeros(self.N, dtype=np.int8)
            dep = np.zeros(self.N, dtype=bool)
            for rid, s, d in self.con.execute("SELECT rowid, source, deprecated FROM docs"):
                src[rid] = SOURCES.index(s)
                dep[rid] = bool(d)
            self._src, self._dep = src, dep
        return self._src, self._dep

    def char_arrays(self):
        if self._char is None:
            ld = lambda n: np.load(self.index / n, mmap_mode="r")  # noqa: E731
            self._char = (ld("char_indptr.npy"), ld("char_indices.npy"),
                          np.load(self.index / "char_idf.npy"), np.load(self.index / "char_norm.npy"))
        return self._char

    def emb(self):
        if self._emb is None:
            self._emb = np.load(self.index / "emb_wordllama.npy", mmap_mode="r")
        return self._emb

    def wordllama(self):
        if self._wl is None:
            self._wl = cm.load_wordllama()
            if self._wl is None:
                self.dense_ok = False
        return self._wl

    # ---- masks ------------------------------------------------------------
    def mask(self, sources=None, include_deprecated=False):
        src, dep = self.src_codes()
        m = np.ones(self.N, dtype=bool)
        if sources:
            m &= np.isin(src, [SOURCES.index(s) for s in sources])
        if not include_deprecated:
            m &= ~dep
        return m

    # ---- retrievers (each returns a list of rowids, best first) ------------
    def bm25(self, query, n=100, sources=None, include_deprecated=False, exclude=None):
        toks = list(dict.fromkeys(cm.tokenize(query)))
        toks = [t for t in toks if re.fullmatch(r"\w+", t)]
        if not toks:
            return []
        expr = " OR ".join('"%s"' % t.replace('"', "") for t in toks)
        expr = "{name body} : (" + expr + ")"
        if sources:
            expr += " AND src : (" + " OR ".join("src" + s for s in sources) + ")"
        sql = ("SELECT rowid FROM fts WHERE fts MATCH ? ORDER BY bm25(fts, 3.0, 1.0, 0.0) LIMIT ?")
        rows = [r[0] for r in self.con.execute(sql, (expr, n + 50))]
        if not include_deprecated:
            _, dep = self.src_codes()
            rows = [r for r in rows if not dep[r]]
        if exclude is not None:
            rows = [r for r in rows if r not in exclude]
        return rows[:n]

    def char(self, query, n=100, sources=None, include_deprecated=False, exclude=None):
        indptr, indices, idf, norm = self.char_arrays()
        feats = sorted({cm.hash_gram(g) for g in cm.char_ngrams(query)})
        feats = [f for f in feats if idf[f] > 0]
        if not feats:
            return []
        scores = np.zeros(self.N, dtype=np.float32)
        for f in feats:
            docs = indices[indptr[f]:indptr[f + 1]]
            scores[docs] += idf[f] * idf[f]
        scores /= norm
        m = self.mask(sources, include_deprecated)
        scores[~m] = 0
        if exclude:
            scores[list(exclude)] = 0
        top = np.argpartition(-scores, min(n, self.N - 1))[:n]
        top = top[np.argsort(-scores[top])]
        return [int(t) for t in top if scores[t] > 0]

    def dense(self, query, n=100, sources=None, include_deprecated=False, exclude=None):
        if not self.dense_ok or self.wordllama() is None:
            return []
        q = np.asarray(self._wl.embed([query], norm=True), dtype=np.float32)[0]
        E = self.emb()
        scores = np.empty(self.N, dtype=np.float32)
        step = 65536
        for i in range(0, self.N, step):
            scores[i:i + step] = E[i:i + step] @ q
        m = self.mask(sources, include_deprecated)
        scores[~m] = -9
        if exclude:
            scores[list(exclude)] = -9
        top = np.argpartition(-scores, n)[:n]
        return [int(t) for t in top[np.argsort(-scores[top])]]

    def qwen_available(self):
        """Optional Qwen3-Embedding channel: needs emb_qwen3*.npy in the index, llama-cpp-python,
        and the GGUF (--qwen-gguf, $MATHDB_QWEN_GGUF, or the file name recorded next to the index)."""
        if self._qwen is None:
            self._qwen = False
            meta = self.index / "emb_qwen3.json"
            if meta.exists() and (self.index / "emb_qwen3.npy").exists():
                import os
                info = json.load(open(meta))
                cands = [self.qwen_gguf, os.environ.get("MATHDB_QWEN_GGUF"), str(self.index / info["model"])]
                gguf = next((c for c in cands if c and Path(c).exists()), None)
                try:
                    import llama_cpp  # noqa: F401
                except Exception:
                    gguf = None
                if gguf:
                    sys.path.insert(0, str(Path(__file__).resolve().parent))
                    from embed_qwen import load_model, QUERY_INSTRUCT
                    E = np.load(self.index / "emb_qwen3.npy")
                    ids_f = self.index / "emb_qwen3_ids.json"
                    if ids_f.exists():  # join on record id (robust to rebuilds / external vectors)
                        ids = json.load(open(ids_f))
                        rowid = {}
                        for i in range(0, len(ids), 500):
                            chunk = ids[i:i + 500]
                            rowid.update(self.con.execute(
                                f"SELECT id, rowid FROM docs WHERE id IN ({','.join('?' * len(chunk))})", chunk))
                        keep = np.array([d in rowid for d in ids], dtype=bool)
                        rows = np.array([rowid[d] for d in ids if d in rowid], dtype=np.int64)
                        E = E[keep]
                    else:
                        rows = np.load(self.index / "emb_qwen3_rows.npy")
                    self._qwen = dict(model=load_model(gguf, threads=1), instruct=QUERY_INSTRUCT, E=E, rows=rows)
        return bool(self._qwen)

    def qwen(self, query, n=100, sources=None, include_deprecated=False, exclude=None):
        """Dense retrieval restricted to the rows that have Qwen3 vectors (ctrl + erdos by default)."""
        if not self.qwen_available():
            return []
        qz = self._qwen
        v = np.asarray(qz["model"].embed([qz["instruct"] + query]), dtype=np.float32)[0]
        v /= np.linalg.norm(v) + 1e-9
        sc = qz["E"] @ v
        rows = qz["rows"]
        m = self.mask(sources, include_deprecated)[rows]
        if exclude:
            m &= ~np.isin(rows, list(exclude))
        sc = np.where(m, sc, -9)
        n = min(n, len(sc) - 1)
        top = np.argpartition(-sc, n)[:n]
        top = top[np.argsort(-sc[top])]
        return [int(rows[t]) for t in top if sc[t] > -9]

    def exact(self, query, sources=None, include_deprecated=False):
        """Exact / suffix name hits for identifier-like queries, plus direct hits for
        `Erdős problem N` / `erdos_N` / `JSP-000123` mentions."""
        q = query.strip()
        hits = []
        m = re.search(r"\berd(?:o|ő|ö|os)s?[\s_#-]*(?:problem[\s#]*)?(\d{1,4})\b", q, re.I)
        if m:
            n = int(m.group(1))
            hits += [r[0] for r in self.con.execute(
                "SELECT rowid FROM docs WHERE (source='erdos' AND name=?) OR (source='fc' AND name IN (?, ?))",
                (f"Erdős Problem {n}", f"Erdos{n}.erdos_{n}", f"erdos_{n}"))]
        for j in re.findall(r"\bJSP-\d{6}\b", q, re.I):
            hits += [r[0] for r in self.con.execute(
                "SELECT rowid FROM docs WHERE source='jsp' AND name LIKE ?", (j.upper() + " %",))]
        if hits:
            src, dep = self.src_codes()
            return [h for h in hits if not sources or SOURCES[src[h]] in sources]
        if not q or " " in q or len(q) > 200:
            return []
        rows = self.con.execute(
            "SELECT rowid, source, deprecated FROM docs WHERE name = ? OR name LIKE ? ESCAPE '\\' LIMIT 50",
            (q, "%." + q.replace("\\", "\\\\").replace("%", "\\%").replace("_", "\\_"))).fetchall()
        out = []
        for rid, s, d in rows:
            if sources and s not in sources:
                continue
            if d and not include_deprecated:
                continue
            out.append(rid)
        return out

    MODES = ("auto", "hybrid2", "hybrid", "hybridq", "bm25", "char", "dense", "qwen")

    def search(self, query, k=10, mode="auto", sources=None, include_deprecated=False, exclude=None,
               pool=100):
        """mode: auto (default) = hybridq if the Qwen3 channel is available, else hybrid2 |
        bm25 | char | dense (WordLlama) | qwen (optional subset channel) |
        hybrid2 = RRF(bm25, char) [best PyPI-only setting] |
        hybrid  = RRF(bm25, char, WordLlama) | hybridq = RRF(bm25, char, Qwen3 subset)."""
        if mode == "auto":  # best measured: hybridq when the optional Qwen channel is installed, else hybrid2
            mode = "hybridq" if self.qwen_available() else "hybrid2"
        kw = dict(sources=sources, include_deprecated=include_deprecated, exclude=exclude)
        single = {"bm25": self.bm25, "char": self.char, "dense": self.dense, "qwen": self.qwen}
        if mode in single:
            return single[mode](query, k, **kw)
        lists = [self.bm25(query, pool, **kw), self.char(query, pool, **kw)]
        if mode == "hybrid" and self.dense_ok:
            lists.append(self.dense(query, pool, **kw))
        if mode == "hybridq" and self.qwen_available():
            lists.append(self.qwen(query, pool, **kw))
        fused = cm.rrf(lists)
        ex = [r for r in self.exact(query, sources, include_deprecated) if not exclude or r not in exclude]
        if ex:
            seen = set(ex)
            fused = ex + [r for r in fused if r not in seen]
        return fused[:k]

    def fetch(self, rowids):
        if not rowids:
            return []
        q = ",".join("?" * len(rowids))
        rows = self.con.execute(
            f"SELECT rowid, id, source, kind, name, module, path, line, statement, doc, url, license, extra "
            f"FROM docs WHERE rowid IN ({q})", rowids).fetchall()
        by = {}
        for r in rows:
            by[r[0]] = dict(id=r[1], source=r[2], kind=r[3], name=r[4], module=r[5], path=r[6], line=r[7],
                            statement=r[8], doc=r[9], url=r[10], license=r[11], extra=json.loads(r[12]))
        return [by[i] for i in rowids if i in by]


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("query")
    ap.add_argument("-k", type=int, default=10)
    ap.add_argument("--source", help="comma list of: " + ",".join(SOURCES))
    ap.add_argument("--mode", default="auto", choices=list(MathDB.MODES),
                    help="auto (default) = hybridq if the optional Qwen3 channel is installed, else hybrid2; "
                         "hybrid2 = RRF(bm25, char); hybrid adds WordLlama; hybridq adds Qwen3 "
                         "(ctrl+erdos rows only); bm25/char/dense/qwen = single retrievers")
    ap.add_argument("--qwen-gguf", help="path to Qwen3-Embedding-0.6B GGUF (optional channel)")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--include-deprecated", action="store_true")
    ap.add_argument("--index", type=Path, default=cm.DEFAULT_INDEX)
    ap.add_argument("--full", action="store_true", help="print full statement/doc in text mode")
    args = ap.parse_args(argv)
    sources = args.source.split(",") if args.source else None
    if sources:
        bad = [s for s in sources if s not in SOURCES]
        if bad:
            ap.error(f"unknown source(s): {bad}")
    t = time.time()
    db = MathDB(args.index, dense=args.mode in ("hybrid", "dense"), qwen_gguf=args.qwen_gguf)
    ids = db.search(args.query, args.k, args.mode, sources, args.include_deprecated)
    res = db.fetch(ids)
    dt = time.time() - t
    if args.json:
        print(json.dumps({"query": args.query, "mode": args.mode, "seconds": round(dt, 3),
                          "results": res}, ensure_ascii=False, indent=1))
        return
    for i, r in enumerate(res, 1):
        loc = f"{r['path']}:{r['line']}" if r["line"] else r["path"]
        tag = r["extra"].get("category") or r["extra"].get("status") or ""
        print(f"{i:2d}. [{r['source']}/{r['kind']}] {r['name']}" + (f"  ({tag})" if tag else ""))
        print(f"    {loc}")
        st = r["statement"] if args.full else r["statement"][:200].replace("\n", " ")
        if st:
            print(f"    : {st}")
        if r["doc"]:
            d = r["doc"] if args.full else r["doc"][:200].replace("\n", " ")
            print(f"    -- {d}")
        if r["url"] and r["url"] != r["path"]:
            print(f"    {r['url']}")
    shown = args.mode if args.mode != "auto" else ("auto->hybridq" if db.qwen_available() else "auto->hybrid2")
    print(f"({len(res)} results, {dt*1000:.0f} ms, mode={shown}{'' if db.dense_ok or args.mode not in ('hybrid', 'dense') else ', WordLlama unavailable'}"
          f"{'' if args.mode not in ('hybridq', 'qwen') or db.qwen_available() else ', Qwen3 channel unavailable'})",
          file=sys.stderr)


if __name__ == "__main__":
    main()
