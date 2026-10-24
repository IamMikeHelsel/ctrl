#!/usr/bin/env python3
"""Build the offline math retrieval index ("mathdb").

    python3 tools/mathdb/build.py [--out DIR] [--corpora DIR] [--no-dense]
                                  [--sources mathlib,ctrl,fc,erdos,jsp,openai]
                                  [--holdout FILE]

Outputs (in --out, default $MATHDB_INDEX or ~/.cache/ctrl-mathdb/index):
  mathdb.sqlite        docs table (all metadata) + FTS5 table for BM25
  char_indptr.npy      CSC postings of hashed char 3-5-grams (feature -> docs)
  char_indices.npy
  char_idf.npy         per-feature idf (float32); char_norm.npy per-doc L2 norm
  emb_wordllama.npy    (N, 256) float32 L2-normalised WordLlama embeddings (optional)
  records.jsonl.gz     every record as JSON (portable dump, also used by eval.py)
  meta.json            corpus revisions, counts, timings, versions

Dependencies: stdlib + numpy (+ pyyaml for plby sources.yaml, + wordllama for
the dense matrix).  See README.md for pinned versions.
"""
from __future__ import annotations

import argparse
import glob
import gzip
import json
import os
import re
import sqlite3
import subprocess
import sys
import time
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common as cm  # noqa: E402
import lean_parse as lp  # noqa: E402

LICENSES = {
    "mathlib": "Apache-2.0",
    "fc": "Apache-2.0",
    "ctrl": "MIT (repo LICENSE; some file headers say Apache-2.0)",
    "erdos": "metadata compiled in ctrl/tools/data (MIT); upstream erdosproblems.com terms not verified",
    "jsp": "metadata compiled in ctrl/tools/data (MIT); upstream TheJustinSunPrize terms not verified",
    "openai": "Apache-2.0 (openai/math LICENSE)",
}


def git_rev(path: Path) -> str | None:
    try:
        return subprocess.run(["git", "-C", str(path), "rev-parse", "HEAD"], capture_output=True,
                              text=True, check=True).stdout.strip()
    except Exception:
        return None


def _deprecated(attrs: str) -> bool:
    return "deprecated" in attrs


# --------------------------------------------------------------------------
# Lean sources

def lean_records(root: Path, files, source: str, url_base: str | None, path_prefix: str = "",
                 module_root: Path | None = None, origin: str | None = None):
    module_root = module_root or root
    recs = []
    for f in files:
        f = Path(f)
        try:
            src = f.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            src = f.read_text(encoding="utf-8", errors="replace")
        rel = f.relative_to(root).as_posix()
        module = f.relative_to(module_root).with_suffix("").as_posix().replace("/", ".")
        for mdoc in lp.module_docs(src)[:1]:
            recs.append(dict(
                source=source, kind="module", name=module, module=module, path=path_prefix + rel,
                line=1, statement="", doc=mdoc[:3000],
                url=(f"{url_base}/{rel}" if url_base else path_prefix + rel),
                extra={"origin": origin} if origin else {}))
        for d in lp.parse_lean(src):
            extra = {}
            if d.attrs:
                extra["attrs"] = d.attrs[:600]
            if _deprecated(d.attrs):
                extra["deprecated"] = True
            if "private" in d.modifiers:
                extra["private"] = True
            if d.anonymous:
                extra["anonymous_instance"] = True
            if d.generated_from:
                extra["generated_by_to_additive_from"] = d.generated_from
            if origin:
                extra["origin"] = origin
            recs.append(dict(
                source=source, kind=d.kind, name=d.name, module=module, path=path_prefix + rel,
                line=d.line, statement=d.signature, doc=d.doc,
                url=(f"{url_base}/{rel}#L{d.line}" if url_base else f"{path_prefix}{rel}:{d.line}"),
                extra=extra))
    return recs


def mathlib_records(C: Path):
    root = C / "mathlib4"
    rev = git_rev(root) or "master"
    files = sorted(glob.glob(str(root / "Mathlib" / "**" / "*.lean"), recursive=True))
    return lean_records(root, files, "mathlib",
                        f"https://github.com/leanprover-community/mathlib4/blob/{rev}"), rev


def ctrl_records(C: Path, repo: Path):
    """ctrl theorems from the working tree plus two archived branches; dedupe by
    (name, module), preferring the working tree, then crossover, then devsnapshot."""
    roots = [
        (repo, sorted(glob.glob(str(repo / "ControlsLean" / "**" / "*.lean"), recursive=True)),
         "ctrl:working-tree", ""),
        (C / "ctrl-crossover" / "lean",
         sorted(glob.glob(str(C / "ctrl-crossover" / "lean" / "**" / "*.lean"), recursive=True)),
         "ctrl:origin/crossover-research-2026-10-19", "crossover:lean/"),
        (C / "ctrl-devsnapshot" / "lean",
         sorted(glob.glob(str(C / "ctrl-devsnapshot" / "lean" / "**" / "*.lean"), recursive=True)),
         "ctrl:origin/backup/20261020/dev-ctrl/snapshot", "devsnapshot:lean/"),
    ]
    seen = {}
    out = []
    raw = 0
    for root, files, origin, prefix in roots:
        for r in lean_records(root, files, "ctrl", None, prefix, origin=origin):
            raw += 1
            key = (r["name"], r["module"], r["kind"] == "module")
            if key in seen:
                seen[key]["extra"].setdefault("also_in", []).append(origin)
                continue
            seen[key] = r
            out.append(r)
    return out, raw


_CAT = re.compile(r"category\s+(research open|research solved|research|test|API|textbook|high_school|undergraduate|graduate|olympiad)")
_AMS = re.compile(r"AMS((?:\s+\d+)+)")
_FP = re.compile(r'formal_proof\s+using\s+(\w+)\s+at\s+"([^"]+)"')


def fc_records(C: Path):
    root = C / "formal-conjectures"
    rev = git_rev(root) or "main"
    files = sorted(glob.glob(str(root / "FormalConjectures" / "**" / "*.lean"), recursive=True))
    recs = lean_records(root, files, "fc",
                        f"https://github.com/google-deepmind/formal-conjectures/blob/{rev}")
    for r in recs:
        parts = r["path"].split("/")
        coll = parts[1] if len(parts) > 2 else ""
        r["extra"]["collection"] = coll
        stem = Path(r["path"]).stem
        if coll == "ErdosProblems" and stem.isdigit():
            r["extra"]["erdos"] = int(stem)
        r["extra"]["problem"] = f"{coll}/{stem}" if coll else stem
        a = r["extra"].get("attrs", "")
        m = _CAT.search(a)
        if m:
            r["extra"]["category"] = m.group(1)
        m = _AMS.search(a)
        if m:
            r["extra"]["ams"] = m.group(1).split()
        fps = _FP.findall(a)
        r["extra"]["formal_proof"] = [u for _, u in fps]
        r["extra"]["has_formal_proof"] = bool(fps)
    return recs, rev


# --------------------------------------------------------------------------
# Erdős / JSP / plby metadata

def erdos_records(C: Path, repo: Path, fc_recs):
    data = repo / "tools" / "data"
    erdos = json.load(open(data / "erdos.json"))["entries"]
    jsp_map = json.load(open(data / "jsp_erdos_map.json"))["mappings"]
    jsp_all = json.load(open(data / "jsp.json"))["entries"]
    erdos_to_jsp = {}
    for j, nums in jsp_map.items():
        for n in nums:
            erdos_to_jsp.setdefault(int(n), []).append(j)
    plby = {}
    try:
        import yaml
        for e in yaml.safe_load(open(C / "plby-lean-proofs" / "data" / "sources.yaml")):
            m = re.match(r"ErdosProblems\.Erdos(\d+)", e.get("key", ""))
            if m:
                plby[int(m.group(1))] = e
    except Exception as ex:  # pyyaml missing: fall back to ctrl's compiled list
        print("warning: plby sources.yaml not parsed:", ex, file=sys.stderr)
        for n in json.load(open(data / "plby_erdos.json"))["solved_erdos"]:
            plby[int(n)] = {}
    fc_main = {}
    fc_files = {}
    for r in fc_recs:
        n = r["extra"].get("erdos")
        if n is None:
            continue
        fc_files[n] = r["path"]
        if r["kind"] in ("theorem", "lemma") and re.fullmatch(rf"(?:Erdos{n}\.)?erdos_{n}", r["name"]):
            fc_main[n] = r
    nums = sorted(set(int(k) for k in erdos) | set(plby))
    recs = []
    for n in nums:
        e = erdos.get(str(n), {})
        p = plby.get(n)
        fcm = fc_main.get(n)
        status = e.get("status", "unknown")
        # JSP titles are independent one-line prose restatements of the same problem
        jsp_titles = [jsp_all[j]["title"] for j in erdos_to_jsp.get(n, []) if j in jsp_all and jsp_all[j].get("title")]
        lines = [f"Erdős Problem #{n}."] + [t.rstrip(".?") + "." for t in jsp_titles] + [f"status: {status}.",
                 f"prize: {e.get('prize', 'unknown')}.", f"formal status: {e.get('formal_status', 'unknown')}."]
        if fcm:
            lines.append(f"formal-conjectures category: {fcm['extra'].get('category', '?')}.")
        if p is not None:
            lines.append("plby/lean-proofs has a Lean proof.")
        if erdos_to_jsp.get(n):
            lines.append("JSP ids: " + ", ".join(erdos_to_jsp[n]) + ".")
        extra = {"erdos": n, "status": status, "prize": e.get("prize"),
                 "formal_status": e.get("formal_status"), "jsp": erdos_to_jsp.get(n, []),
                 "fc_file": fc_files.get(n), "plby": p is not None}
        if p:
            extra["plby_urls"] = p.get("url", [])
            extra["plby_arxiv"] = p.get("arxiv")
            auth = p.get("author") or {}
            inf = auth.get("informal") if isinstance(auth, dict) else None
            extra["plby_informal_authors"] = (inf.get("human", []) if isinstance(inf, dict)
                                              else (inf if isinstance(inf, list) else []))
        if fcm:
            extra["fc_main"] = fcm["name"]
            extra["fc_category"] = fcm["extra"].get("category")
            extra["fc_has_formal_proof"] = fcm["extra"].get("has_formal_proof")
        recs.append(dict(
            source="erdos", kind="erdos_problem", name=f"Erdős Problem {n}", module="erdosproblems.com",
            path=fc_files.get(n) or "", line=0, statement=" ".join(lines),
            doc=(fcm["doc"] if fcm else ""), url=f"https://www.erdosproblems.com/{n}", extra=extra))
    jsp = json.load(open(data / "jsp.json"))["entries"]
    for j, e in jsp.items():
        recs.append(dict(
            source="jsp", kind="jsp_problem", name=f"{j} {e.get('title', '')}".strip(), module="JSP",
            path=next((fc_files[int(n)] for n in jsp_map.get(j, []) if int(n) in fc_files), ""), line=0,
            statement=f"{j}: {e.get('title', '')}. status: {e.get('status')}. lean: {e.get('lean')}. "
                      f"eligible: {e.get('eligible')}. erdos: {jsp_map.get(j, [])}",
            doc="", url=(e.get("lean_urls") or [""])[0],
            extra={"jsp": j, "status": e.get("status"), "lean": e.get("lean"),
                   "lean_urls": e.get("lean_urls", []), "eligible": e.get("eligible"),
                   "erdos": jsp_map.get(j, [])}))
    return recs, len(plby)


# --------------------------------------------------------------------------
# OpenAI math manuscripts (titles, abstracts, theorem-like statements)

_THM_ENV = re.compile(
    r"\\begin\{((?:main)?theorem\*?|thm\*?|conjecture\*?|proposition\*?|corollary\*?|maintheorem\*?|theoremA\*?)\}"
    r"(\[[^\]]*\])?(.*?)\\end\{\1\}", re.S)


def _clean_md(s: str) -> str:
    s = re.sub(r"<[^>]+>", "", s)
    s = s.replace("&emsp;", " ").replace("$`", "$").replace("`$", "$")
    return re.sub(r"\s+", " ", s).strip()


def openai_records(C: Path):
    root = C / "openai-math"
    rev = git_rev(root) or "main"
    base = f"https://github.com/openai/math/blob/{rev}"
    txt = (root / "CONTENTS.md").read_text(encoding="utf-8")
    recs = []
    family = None
    cells = re.findall(r"<td>(.*?)</td>", txt, re.S)
    for cell in cells:
        cell = cell.strip()
        m = re.match(r"\*\*(\d{3})\.\s*(.*?)\*\*\s*(.*)", cell, re.S)
        if m:
            family = m.group(1)
            recs.append(dict(source="openai", kind="family", name=f"OAI family {family}: {_clean_md(m.group(2))}",
                             module="openai/math CONTENTS.md", path="CONTENTS.md", line=0,
                             statement=_clean_md(m.group(2)), doc=_clean_md(m.group(3)),
                             url=f"{base}/CONTENTS.md", extra={"family": family}))
            continue
        m = re.match(r"(?:&emsp;)?\s*\[(.*?)\]\((preprints/[^)]+)\)\s*(.*)", cell, re.S)
        if m:
            title, link, abstract = _clean_md(m.group(1)), m.group(2), _clean_md(m.group(3))
            d = link.split("/")[1]
            recs.append(dict(source="openai", kind="manuscript", name=title, module=f"preprints/{d}",
                             path=link, line=0, statement=title, doc=abstract, url=f"{base}/{link}",
                             extra={"family": family, "dir": d}))
            # theorem-like statements from the LaTeX sources
            n_thm = 0
            for tex in sorted((root / "preprints" / d).rglob("*.tex")):
                try:
                    t = tex.read_text(encoding="utf-8", errors="replace")
                except Exception:
                    continue
                t = re.sub(r"(?<!\\)%.*", "", t)
                for mm in _THM_ENV.finditer(t):
                    body = re.sub(r"\\label\{[^}]*\}", "", mm.group(3))
                    body = re.sub(r"\s+", " ", body).strip()
                    if len(body) < 30:
                        continue
                    n_thm += 1
                    if n_thm > 40:
                        break
                    env = mm.group(1).rstrip("*")
                    note = (mm.group(2) or "").strip("[]")
                    line = t[:mm.start()].count("\n") + 1
                    rel = tex.relative_to(root).as_posix()
                    recs.append(dict(source="openai", kind=f"tex_{env}",
                                     name=f"{title} — {env}{(' (' + note + ')') if note else ''} #{n_thm}",
                                     module=f"preprints/{d}", path=rel, line=line,
                                     statement=body[:1500], doc="", url=f"{base}/{rel}#L{line}",
                                     extra={"family": family, "dir": d}))
                if n_thm > 40:
                    break
    return recs, rev


# --------------------------------------------------------------------------
# Index writing

def assign_ids(recs):
    seen = {}
    for r in recs:
        base = f"{r['source']}:{r['name']}" if r["kind"] != "module" else f"{r['source']}:module:{r['name']}"
        if base in seen:
            seen[base] += 1
            r["id"] = f"{base}@{r['path']}:{r['line']}"
            if r["id"] in seen:
                r["id"] += f"#{seen[base]}"
        else:
            seen[base] = 0
            r["id"] = base
        r["license"] = LICENSES[r["source"]]


def fts_fields(r):
    name_toks = cm.tokenize(r["name"]) + cm.humanize_name(r["name"]).split()
    body = " ".join([r.get("doc") or "", r.get("statement") or "", r.get("module") or ""])
    extra = r.get("extra", {})
    tags = []
    for k in ("category", "status", "collection", "fc_category"):
        if extra.get(k):
            tags.append(str(extra[k]))
    if extra.get("erdos") is not None and r["source"] in ("fc", "erdos"):
        tags.append(f"erdos {extra['erdos']}")
    body_toks = cm.tokenize(body + " " + " ".join(tags) + " " + r["kind"])
    return " ".join(name_toks), " ".join(body_toks)


def write_sqlite(path: Path, recs):
    if path.exists():
        path.unlink()
    con = sqlite3.connect(path)
    con.execute("PRAGMA journal_mode=OFF")
    con.execute("PRAGMA synchronous=OFF")
    con.execute("""CREATE TABLE docs(
        rowid INTEGER PRIMARY KEY, id TEXT UNIQUE, source TEXT, kind TEXT, name TEXT,
        module TEXT, path TEXT, line INTEGER, statement TEXT, doc TEXT, url TEXT,
        license TEXT, deprecated INTEGER, extra TEXT)""")
    con.execute("""CREATE VIRTUAL TABLE fts USING fts5(
        name, body, src, content='', tokenize='porter unicode61 remove_diacritics 2')""")
    rows = []
    frows = []
    for i, r in enumerate(recs):
        rows.append((i, r["id"], r["source"], r["kind"], r["name"], r["module"], r["path"], r["line"],
                     r["statement"], r["doc"], r["url"], r["license"],
                     1 if r["extra"].get("deprecated") else 0, json.dumps(r["extra"], ensure_ascii=False)))
        n, b = fts_fields(r)
        frows.append((i, n, b, "src" + r["source"]))
    con.executemany("INSERT INTO docs VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)", rows)
    con.executemany("INSERT INTO fts(rowid, name, body, src) VALUES (?,?,?,?)", frows)
    con.execute("CREATE INDEX docs_name ON docs(name)")
    con.execute("CREATE INDEX docs_source ON docs(source)")
    con.execute("INSERT INTO fts(fts) VALUES('optimize')")
    con.commit()
    con.execute("VACUUM")
    con.close()


def write_char(out: Path, recs, max_df_frac: float = 0.2):
    N = len(recs)
    feats = []
    docs = []
    for i, r in enumerate(recs):
        h = np.fromiter((cm.hash_gram(g) for g in cm.char_ngrams(cm.char_text(r))), dtype=np.int32)
        h = np.unique(h)
        feats.append(h)
        docs.append(np.full(len(h), i, dtype=np.int32))
    feats = np.concatenate(feats)
    docs = np.concatenate(docs)
    df = np.bincount(feats, minlength=cm.CHAR_DIM).astype(np.int64)
    idf = np.log((N + 1) / (df + 1)).astype(np.float32) + 1.0
    idf[df > max_df_frac * N] = 0.0          # drop ubiquitous grams (stop-grams)
    keep = idf[feats] > 0
    feats, docs = feats[keep], docs[keep]
    order = np.argsort(feats, kind="stable")
    feats, docs = feats[order], docs[order]
    indptr = np.zeros(cm.CHAR_DIM + 1, dtype=np.int64)
    np.cumsum(np.bincount(feats, minlength=cm.CHAR_DIM), out=indptr[1:])
    norm = np.sqrt(np.bincount(docs, weights=(idf[feats].astype(np.float64) ** 2), minlength=N)).astype(np.float32)
    norm[norm == 0] = 1.0
    np.save(out / "char_indptr.npy", indptr)
    np.save(out / "char_indices.npy", docs.astype(np.int32))
    np.save(out / "char_idf.npy", idf)
    np.save(out / "char_norm.npy", norm)
    return int(len(docs))


def write_dense(out: Path, recs, batch: int = 4096):
    wl = cm.load_wordllama()
    if wl is None:
        print("wordllama not importable; skipping dense embeddings", file=sys.stderr)
        return None
    texts = [cm.dense_text(r) for r in recs]
    embs = []
    for i in range(0, len(texts), batch):
        e = np.asarray(wl.embed(texts[i:i + batch], norm=True), dtype=np.float32)
        embs.append(e)
    E = np.concatenate(embs)
    np.save(out / "emb_wordllama.npy", E)
    return E.shape


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--out", type=Path, default=cm.DEFAULT_INDEX)
    ap.add_argument("--corpora", type=Path, default=cm.DEFAULT_CORPORA)
    ap.add_argument("--repo", type=Path, default=cm.REPO)
    ap.add_argument("--sources", default="mathlib,ctrl,fc,erdos,jsp,openai")
    ap.add_argument("--no-dense", action="store_true")
    ap.add_argument("--holdout", type=Path,
                    help="file with one record id per line whose docstring is removed (for eval)")
    args = ap.parse_args(argv)
    srcs = set(args.sources.split(","))
    C = args.corpora
    args.out.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    timings = {}
    meta = {"corpora": {}, "counts": {}, "timings": timings}
    recs = []

    def tick(name, t):
        timings[name] = round(time.time() - t, 2)
        print(f"[{timings[name]:7.1f}s] {name}", file=sys.stderr)

    fc = []
    if "mathlib" in srcs:
        t = time.time()
        r, rev = mathlib_records(C)
        recs += r
        meta["corpora"]["mathlib4"] = rev
        tick("parse mathlib", t)
    if "ctrl" in srcs:
        t = time.time()
        r, raw = ctrl_records(C, args.repo)
        recs += r
        meta["counts"]["ctrl_raw_before_dedupe"] = raw
        tick("parse ctrl", t)
    if "fc" in srcs or "erdos" in srcs:
        t = time.time()
        fc, rev = fc_records(C)
        meta["corpora"]["formal-conjectures"] = rev
        if "fc" in srcs:
            recs += fc
        tick("parse formal-conjectures", t)
    if "erdos" in srcs or "jsp" in srcs:
        t = time.time()
        r, nplby = erdos_records(C, args.repo, fc)
        recs += [x for x in r if x["source"] in srcs]
        meta["corpora"]["plby-lean-proofs"] = git_rev(C / "plby-lean-proofs")
        meta["counts"]["plby_erdos_entries"] = nplby
        tick("erdos/jsp metadata", t)
    if "openai" in srcs:
        t = time.time()
        r, rev = openai_records(C)
        recs += r
        meta["corpora"]["openai-math"] = rev
        tick("openai manuscripts", t)

    assign_ids(recs)
    if args.holdout:
        hold = set(x.strip() for x in open(args.holdout) if x.strip())
        n = 0
        for r in recs:
            if r["id"] in hold:
                r["doc"] = ""
                n += 1
        meta["holdout"] = {"file": str(args.holdout), "requested": len(hold), "applied": n}
        print(f"holdout: removed docstrings of {n}/{len(hold)} records", file=sys.stderr)

    from collections import Counter
    meta["counts"]["by_source"] = dict(Counter(r["source"] for r in recs))
    meta["counts"]["by_source_kind"] = {f"{k[0]}/{k[1]}": v for k, v in
                                        sorted(Counter((r["source"], r["kind"]) for r in recs).items())}
    meta["counts"]["total"] = len(recs)
    meta["counts"]["with_docstring"] = dict(Counter(r["source"] for r in recs if r["doc"]))

    t = time.time()
    with gzip.open(args.out / "records.jsonl.gz", "wt", encoding="utf-8") as f:
        for r in recs:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")
    tick("records.jsonl.gz", t)
    t = time.time()
    write_sqlite(args.out / "mathdb.sqlite", recs)
    srcs_order = ("mathlib", "ctrl", "fc", "erdos", "jsp", "openai")  # must match query.SOURCES
    np.save(args.out / "src.npy", np.array([srcs_order.index(r["source"]) for r in recs], dtype=np.int8))
    np.save(args.out / "dep.npy", np.array([bool(r["extra"].get("deprecated")) for r in recs], dtype=bool))
    tick("sqlite + fts5", t)
    t = time.time()
    meta["counts"]["char_postings"] = write_char(args.out, recs)
    tick("char n-gram postings", t)
    if not args.no_dense:
        t = time.time()
        shape = write_dense(args.out, recs)
        meta["dense"] = {"model": "wordllama l2_supercat_256 (bundled in wheel)", "shape": shape}
        tick("wordllama embeddings", t)
    elif (args.out / "emb_wordllama.npy").exists():
        (args.out / "emb_wordllama.npy").unlink()
    timings["total"] = round(time.time() - t0, 2)
    try:
        import importlib.metadata as im
        meta["versions"] = {p: im.version(p) for p in ("numpy", "wordllama", "PyYAML")
                            if _has_dist(im, p)}
    except Exception:
        pass
    meta["python"] = sys.version.split()[0]
    meta["sqlite"] = sqlite3.sqlite_version
    meta["built_at"] = time.strftime("%Y-%m-%dT%H:%M:%S%z")
    meta["sizes_bytes"] = {p.name: p.stat().st_size for p in sorted(args.out.iterdir()) if p.is_file()}
    json.dump(meta, open(args.out / "meta.json", "w"), indent=2, ensure_ascii=False)
    print(json.dumps({"total": len(recs), "by_source": meta["counts"]["by_source"],
                      "seconds": timings["total"]}, indent=1), file=sys.stderr)


def _has_dist(im, p):
    try:
        im.version(p)
        return True
    except Exception:
        return False


if __name__ == "__main__":
    main()
