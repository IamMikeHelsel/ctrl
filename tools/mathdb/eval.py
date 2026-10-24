#!/usr/bin/env python3
"""Labelled retrieval evaluation for mathdb.

Step 1 (once): write the query set + hold-out list from a built index
    python3 tools/mathdb/eval.py make-queries --index <main index>
  -> tools/mathdb/eval/queries.jsonl, tools/mathdb/eval/holdout_ids.txt

Step 2: build an evaluation index whose held-out docstrings are removed
    python3 tools/mathdb/build.py --out <eval index> --holdout tools/mathdb/eval/holdout_ids.txt

Step 3: score every retriever
    python3 tools/mathdb/eval.py run --index <eval index> [--json out.json]

Query groups:
  mathlib_heldout  Mathlib docstring -> declaration (docstring removed from the eval index)
  mathlib_nl       hand-written natural-language names of well-known theorems -> Mathlib decl(s)
  ctrl_nl          hand-written control/estimation/robotics/vision paraphrases -> ctrl theorem(s)
  erdos_prose      hand-written paraphrase of an Erdős problem -> formal-conjectures file
Relevance: name groups count a hit if the result's name is one of the targets;
erdos_prose counts a hit if the result's path is FormalConjectures/ErdosProblems/<n>.lean.
"""
from __future__ import annotations

import argparse
import gzip
import json
import random
import re
import statistics
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common as cm  # noqa: E402
from query import MathDB  # noqa: E402

EVAL_DIR = Path(__file__).resolve().parent / "eval"

MATHLIB_NL = [
    ("Euclid: there are infinitely many prime numbers", ["Nat.exists_infinite_primes", "Nat.infinite_setOf_prime"]),
    ("Cauchy-Schwarz inequality for a real inner product space",
     ["real_inner_mul_inner_self_le", "abs_real_inner_le_norm", "real_inner_le_norm", "norm_inner_le_norm"]),
    ("intermediate value theorem on a closed interval", ["intermediate_value_Icc", "intermediate_value_Icc'"]),
    ("fundamental theorem of calculus: integrating a derivative gives the difference of endpoint values",
     ["intervalIntegral.integral_eq_sub_of_hasDerivAt", "intervalIntegral.integral_deriv_eq_sub"]),
    ("mean value theorem: the derivative equals the slope at some interior point",
     ["exists_deriv_eq_slope", "exists_hasDerivAt_eq_slope"]),
    ("Fermat's little theorem a^(p-1) = 1 modulo a prime", ["ZMod.pow_card_sub_one_eq_one", "ZMod.pow_card"]),
    ("Lagrange's theorem: order of a subgroup divides the order of the group", ["Subgroup.card_subgroup_dvd_card"]),
    ("Bezout identity: the gcd is an integer linear combination", ["Nat.gcd_eq_gcd_ab", "Int.gcd_eq_gcd_ab"]),
    ("Cayley-Hamilton theorem: a square matrix satisfies its own characteristic polynomial",
     ["Matrix.aeval_self_charpoly"]),
    ("Bolzano-Weierstrass: every bounded sequence has a convergent subsequence",
     ["tendsto_subseq_of_bounded", "tendsto_subseq_of_frequently_bounded"]),
    ("a continuous function on a compact set attains its maximum", ["IsCompact.exists_isMaxOn"]),
    ("Banach fixed point theorem for a contraction on a complete metric space",
     ["ContractingWith.exists_fixedPoint", "ContractingWith.fixedPoint_isFixedPt"]),
    ("weighted arithmetic mean geometric mean inequality", ["Real.geom_mean_le_arith_mean_weighted"]),
    ("the square root of two is irrational", ["irrational_sqrt_two"]),
    ("Wilson's theorem: (p-1)! is congruent to -1 mod p", ["ZMod.wilsons_lemma"]),
    ("law of quadratic reciprocity for Legendre symbols",
     ["legendreSym.quadratic_reciprocity", "legendreSym.quadratic_reciprocity'"]),
    ("Heine-Borel: in a proper metric space a set is compact iff closed and bounded",
     ["Metric.isCompact_iff_isClosed_bounded"]),
    ("binomial theorem for the expansion of (x + y)^n", ["add_pow", "Commute.add_pow"]),
    ("determinant of a product of two matrices is the product of determinants", ["Matrix.det_mul"]),
    ("sum of a geometric series with ratio less than one", ["tsum_geometric_of_lt_one"]),
    ("existence of a Sylow p-subgroup of a finite group", ["Sylow.exists_subgroup_card_pow_prime", "Sylow.nonempty"]),
    ("fundamental theorem of algebra: every nonconstant complex polynomial has a root", ["Complex.exists_root"]),
    ("pigeonhole principle: a map from a larger finite set to a smaller one is not injective",
     ["Finset.exists_ne_map_eq_of_card_lt_of_maps_to", "Fintype.exists_ne_map_eq_of_card_lt"]),
    ("the harmonic series diverges",
     ["Real.not_summable_natCast_inv", "Real.not_summable_one_div_natCast",
      "Real.tendsto_sum_range_one_div_nat_succ_atTop"]),
    ("Euler's criterion for quadratic residues modulo a prime", ["ZMod.euler_criterion"]),
    ("a prime congruent to 1 mod 4 is a sum of two squares", ["Nat.Prime.sq_add_sq"]),
    ("Basel problem: sum of reciprocals of squares equals pi squared over six", ["hasSum_zeta_two"]),
    ("determinant of the transpose of a matrix", ["Matrix.det_transpose"]),
]

P = "ControlsLean."
CTRL_NL = [
    ("discrete algebraic Riccati equation uniqueness under detectability", [P + "Controls.dare_unique_of_detectable"]),
    ("output feedback LQG separation: closed loop is stable if the plant is stabilizable and detectable",
     [P + "Controls.lqg_closed_loop_stable_of_stabilizable_detectable"]),
    ("discrete-time control barrier function keeps the safe set forward invariant",
     [P + "Controls.dtcbf_forward_invariant"]),
    ("a system in companion (controllable canonical) form is controllable", [P + "Controls.controllable_companion"]),
    ("converse Lyapunov theorem for Schur stable matrices", [P + "Controls.converse_lyapunov_of_schur"]),
    ("stabilizability alone gives a positive semidefinite solution of the Riccati equation",
     [P + "Controls.dare_exists_of_stabilizable_psd"]),
    ("the stabilizing Riccati solution is the largest PSD solution", [P + "Controls.dare_le_of_stabilizing"]),
    ("input-to-state stable system trajectories are ultimately bounded", [P + "Controls.iss_ultimate_bound"]),
    ("Jury stability criterion for a second order discrete polynomial", [P + "Controls.isSchur2_iff_jury"]),
    ("Ackermann formula for pole placement of the closed-loop characteristic polynomial",
     [P + "Controls.pole_placement_charpoly"]),
    ("Luenberger observer estimation error evolves by A minus L C", [P + "Controls.observer_error_step"]),
    ("matrix inversion lemma Sherman Morrison Woodbury", [P + "Estimation.woodbury_left_inv"]),
    ("least squares minimizer characterized by the normal equations", [P + "Estimation.isLeastSquares_iff"]),
    ("Kalman gain minimizes the trace of the posterior error covariance (MMSE optimality)",
     [P + "Estimation.trace_josephCov_le", P + "Estimation.trace_josephCov_le_of_psd"]),
    ("POMDP value function is attained by some alpha vector",
     [P + "Estimation.POMDPBelief.exists_alpha_achieving_pomdpValue"]),
    ("two-link planar arm Jacobian is singular exactly when the elbow angle sine vanishes",
     [P + "Robotics.det_jacobian_eq_zero_iff"]),
    ("quaternion attitude kinematics conserve the quaternion norm", [P + "Robotics.hasDerivAt_normSq_kinematics"]),
    ("PD plus gravity compensation for a robot manipulator dissipates energy",
     [P + "Robotics.manipulator_pd_gravity_lyapunov"]),
    ("transpose of Rodrigues rotation equals rotation by the opposite angle", [P + "Robotics.rodrigues_transpose"]),
    ("eight point algorithm recovers the essential matrix up to scale", [P + "Vision.eq_smul_essential"]),
    ("cross ratio is invariant under projective transformations",
     [P + "Vision.crossRatio_mulVec", P + "Vision.crossRatioAffine_mobius",
      P + "Vision.crossRatio_collinear_homography", P + "Vision.crossRatioFrom_homography"]),
    ("recursive feasibility of model predictive control",
     [P + "Controls.mpc_feasible_step", P + "Controls.lti_mpc_recursive_feasibility_step"]),
    ("H-infinity Riccati solution gives Schur stability under detectability", [P + "Controls.hinf_schur_of_detectable"]),
    ("small gain theorem for a feedback interconnection of two finite-gain systems",
     [P + "Controls.small_gain", P + "Controls.small_gain_left", P + "Controls.small_gain_linear"]),
    ("controllability Gramian steering: invertible Gramian lets you reach any state", [P + "Controls.gramian_steer"]),
    ("unicycle robot cannot slip sideways (nonholonomic constraint)", [P + "Robotics.nonholonomic_constraint"]),
]

ERDOS_PROSE = [
    ("n positive integers with all subset sums distinct force the largest element to be at least a constant times 2^n", 1),
    ("can the least modulus of a covering system with distinct moduli be arbitrarily large", 2),
    ("if a set of integers has divergent sum of reciprocals must it contain arbitrarily long arithmetic progressions", 3),
    ("infinitely often the gap between consecutive primes is larger than C log n times an iterated-log factor", 4),
    ("three consecutive prime gaps that are strictly increasing occur infinitely often", 6),
    ("does there exist a covering system all of whose moduli are odd", 7),
    ("sunflower problem: how large must a family of n-element sets be to contain a k-sunflower", 20),
    ("an additive basis of order two must have an unbounded number of representations", 28),
    ("largest Sidon subset of 1..N has size square root of N plus a small error", 30),
    ("minimum overlap problem for a set and its complement", 36),
    ("an infinite Sidon sequence whose counting function is nearly square root of N", 39),
    ("sum-product: for a finite set of integers the sumset or the product set is almost quadratic in size", 52),
    ("graph of minimum degree three contains a cycle whose length is a power of two", 64),
    ("limit of the k-th root of the diagonal Ramsey number", 77),
    ("n points in the plane determine at least n over root log n distinct distances", 89),
    ("maximum number of unit distances determined by n points in the plane", 90),
    ("asymptotic formula for the largest subset of 1..N with no k-term arithmetic progression", 142),
    ("4/n can always be written as a sum of three unit fractions", 242),
]


def load_records(index: Path):
    with gzip.open(index / "records.jsonl.gz", "rt", encoding="utf-8") as f:
        for line in f:
            yield json.loads(line)


def make_queries(args):
    rng = random.Random(args.seed)
    cands = []
    for r in load_records(args.index):
        if r["source"] != "mathlib" or r["kind"] not in ("theorem", "lemma", "def", "abbrev", "structure", "class"):
            continue
        if r["extra"].get("deprecated") or r["extra"].get("private") or not r["statement"]:
            continue
        d = r["doc"]
        if not (60 <= len(d) <= 400):
            continue
        cands.append(r)
    cands.sort(key=lambda r: r["id"])
    sample = rng.sample(cands, args.n_heldout)
    EVAL_DIR.mkdir(exist_ok=True)
    out = []
    for r in sample:
        last = r["name"].split(".")[-1]
        q = re.sub(r"`[^`]*`", lambda m: "" if last in m.group(0) else m.group(0), r["doc"])
        q = re.sub(r"\s+", " ", q).strip()
        out.append({"group": "mathlib_heldout", "query": q, "targets": [r["name"]], "target_id": r["id"]})
    for q, t in MATHLIB_NL:
        out.append({"group": "mathlib_nl", "query": q, "targets": t})
    for q, t in CTRL_NL:
        out.append({"group": "ctrl_nl", "query": q, "targets": t})
    for q, n in ERDOS_PROSE:
        out.append({"group": "erdos_prose", "query": q, "erdos": n,
                    "target_path": f"FormalConjectures/ErdosProblems/{n}.lean"})
    with open(EVAL_DIR / "queries.jsonl", "w", encoding="utf-8") as f:
        for o in out:
            f.write(json.dumps(o, ensure_ascii=False) + "\n")
    with open(EVAL_DIR / "holdout_ids.txt", "w", encoding="utf-8") as f:
        for r in sample:
            f.write(r["id"] + "\n")
    print(f"wrote {len(out)} queries ({args.n_heldout} held-out) to {EVAL_DIR}")


RETRIEVERS = ["bm25", "char", "dense", "hybrid2", "hybrid"]
QWEN_RETRIEVERS = ["qwen", "hybridq"]
LEANSEARCH_FIELDS = ["q1a_lean", "q1b_latex", "q1c_natural", "q2_slogan", "q3_nickname", "q4_special_case"]


def leansearch(args):
    """LeanSearch-v2 MathlibQR benchmark (Apache-2.0, frenzymath/LeanSearch-v2/benchmark/MathlibQR.json):
    200 gold Mathlib declarations x up to 6 query styles.  One relevant item per query, so
    nDCG@10 = 1/log2(1+rank) if rank<=10 else 0.  Searched with --source mathlib."""
    import math
    gold = json.load(open(args.benchmark, encoding="utf-8"))
    db = MathDB(args.index)
    rets = list(args.retrievers.split(","))
    exists = {g["full_name"]: bool(db.con.execute("SELECT 1 FROM docs WHERE name=? AND source='mathlib' LIMIT 1",
                                                  (g["full_name"],)).fetchone()) for g in gold}
    qs = [(g, f, g[f]) for g in gold for f in LEANSEARCH_FIELDS if (g.get(f) or "").strip()]
    for m in rets:
        db.search("warm up", 10, m, sources=["mathlib"])
    ranks = {m: [] for m in rets}
    lat = {m: [] for m in rets}
    for g, f, q in qs:
        for m in rets:
            t = time.time()
            ids = db.search(q, args.k, m, sources=["mathlib"])
            lat[m].append(time.time() - t)
            order = {rid: i for i, rid in enumerate(ids)}
            rk = None
            for rid, name in db.con.execute(
                    f"SELECT rowid, name FROM docs WHERE rowid IN ({','.join('?' * len(ids))})", ids) if ids else []:
                if name == g["full_name"]:
                    r = order[rid] + 1
                    rk = r if rk is None else min(rk, r)
            ranks[m].append((f, exists[g["full_name"]], rk))

    def agg(rows):
        n = len(rows)
        if not n:
            return {}
        nd = sum(1 / math.log2(1 + r) for _, _, r in rows if r) / n
        return {"n": n, "nDCG@10": nd, "R@1": sum(1 for *_, r in rows if r == 1) / n,
                "R@10": sum(1 for *_, r in rows if r) / n, "MRR@10": sum(1 / r for *_, r in rows if r) / n}

    out = {}
    print(f"LeanSearch-v2 MathlibQR: {len(gold)} gold decls ({sum(exists.values())} exist in index), "
          f"{len(qs)} queries, k={args.k}, source=mathlib")
    for scope in ("all", "gold_exists"):
        print(f"\n### scope={scope}\n\n| retriever | n | nDCG@10 | R@1 | R@10 | MRR@10 | median ms |\n|---|---|---|---|---|---|---|")
        for m in rets:
            rows = [x for x in ranks[m] if scope == "all" or x[1]]
            a = agg(rows)
            out[f"{scope}/{m}"] = a
            print(f"| {m} | {a['n']} | {a['nDCG@10']:.3f} | {a['R@1']:.3f} | {a['R@10']:.3f} | {a['MRR@10']:.3f} | "
                  f"{1000 * statistics.median(lat[m]):.0f} |")
    print("\n### nDCG@10 by query style (scope=all)\n")
    print("| style | n | " + " | ".join(rets) + " |\n|---|---|" + "---|" * len(rets))
    for f in LEANSEARCH_FIELDS:
        cells = []
        n = 0
        for m in rets:
            a = agg([x for x in ranks[m] if x[0] == f])
            n = a.get("n", 0)
            cells.append(f"{a.get('nDCG@10', 0):.3f}")
            out[f"style/{f}/{m}"] = a
        print(f"| {f} | {n} | " + " | ".join(cells) + " |")
    if args.json:
        json.dump(out, open(args.json, "w"), indent=1)


def run(args):
    qs = [json.loads(l) for l in open(args.queries, encoding="utf-8")]
    db = MathDB(args.index)
    global RETRIEVERS
    RETRIEVERS = args.retrievers.split(",")
    # validate targets exist
    missing = []
    for q in qs:
        for t in q.get("targets", []):
            if not db.con.execute("SELECT 1 FROM docs WHERE name=? LIMIT 1", (t,)).fetchone():
                missing.append(t)
    if missing:
        print("WARNING targets not in index:", missing, file=sys.stderr)
    # warm up
    for m in RETRIEVERS:
        db.search("warm up query prime", 10, m)
    K = args.k
    results = {m: {} for m in RETRIEVERS}
    lat = {m: [] for m in RETRIEVERS}
    per_query = []
    for q in qs:
        row = {"group": q["group"], "query": q["query"][:120]}
        for m in RETRIEVERS:
            t = time.time()
            ids = db.search(q["query"], K, m)
            lat[m].append(time.time() - t)
            recs = db.fetch(ids)
            rank = None
            for i, r in enumerate(recs):
                if q["group"] == "erdos_prose":
                    ok = r["path"] == q["target_path"]
                else:
                    ok = r["name"] in q["targets"]
                if ok:
                    rank = i + 1
                    break
            results[m].setdefault(q["group"], []).append(rank)
            row[m] = rank
            if q["group"] == "erdos_prose":
                # strict: only formal-conjectures / erdos rows count (JSP rows also carry the FC path)
                strict = next((i + 1 for i, r in enumerate(recs)
                               if r["path"] == q["target_path"] and r["source"] in ("fc", "erdos")), None)
                results[m].setdefault("erdos_prose_strict", []).append(strict)
            if m == RETRIEVERS[-1]:
                row["top3"] = [r["name"] for r in recs[:3]]
        per_query.append(row)

    def metrics(ranks):
        n = len(ranks)
        r = lambda k: sum(1 for x in ranks if x and x <= k) / n  # noqa: E731
        mrr = sum(1.0 / x for x in ranks if x) / n
        return {"n": n, "R@1": r(1), "R@5": r(5), "R@10": r(10), f"MRR@{K}": mrr}

    order = ["mathlib_heldout", "mathlib_nl", "ctrl_nl", "erdos_prose"]
    groups = sorted({q["group"] for q in qs}, key=order.index)
    table = {}
    for m in RETRIEVERS:
        table[m] = {g: metrics(results[m][g]) for g in groups}
        table[m]["ALL"] = metrics([x for g in groups for x in results[m][g]])
        if "erdos_prose_strict" in results[m]:
            table[m]["erdos_prose_strict"] = metrics(results[m]["erdos_prose_strict"])
        table[m]["latency_ms"] = {
            "median": round(1000 * statistics.median(lat[m]), 1),
            "p95": round(1000 * sorted(lat[m])[int(0.95 * (len(lat[m]) - 1))], 1),
        }
    # print markdown
    print(f"index: {args.index}   queries: {len(qs)}   k={K}   dense={'yes' if db.dense_ok else 'no'}")
    for g in groups + (["erdos_prose_strict"] if "erdos_prose" in groups else []) + ["ALL"]:
        n = table[RETRIEVERS[0]][g]["n"]
        print(f"\n### {g} (n={n})\n")
        print(f"| retriever | R@1 | R@5 | R@10 | MRR@{K} |")
        print("|---|---|---|---|---|")
        for m in RETRIEVERS:
            t = table[m][g]
            print(f"| {m} | {t['R@1']:.3f} | {t['R@5']:.3f} | {t['R@10']:.3f} | {t[f'MRR@{K}']:.3f} |")
    print("\n### warm query latency (ms, search call only, top-%d; metadata fetch excluded)\n" % K)
    print("| retriever | median | p95 |")
    print("|---|---|---|")
    for m in RETRIEVERS:
        print(f"| {m} | {table[m]['latency_ms']['median']} | {table[m]['latency_ms']['p95']} |")
    if args.json:
        json.dump({"table": table, "per_query": per_query}, open(args.json, "w"), indent=1, ensure_ascii=False)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    a = sub.add_parser("make-queries")
    a.add_argument("--index", type=Path, default=cm.DEFAULT_INDEX)
    a.add_argument("--n-heldout", type=int, default=40)
    a.add_argument("--seed", type=int, default=20261024)
    b = sub.add_parser("run")
    b.add_argument("--index", type=Path, required=True)
    b.add_argument("--queries", type=Path, default=EVAL_DIR / "queries.jsonl")
    b.add_argument("-k", type=int, default=10)
    b.add_argument("--json", type=Path)
    b.add_argument("--retrievers", default=",".join(RETRIEVERS),
                   help="comma list; add qwen,hybridq when the optional Qwen3 channel is built")
    c = sub.add_parser("leansearch")
    c.add_argument("--index", type=Path, default=cm.DEFAULT_INDEX)
    c.add_argument("--benchmark", type=Path, required=True, help="LeanSearch-v2 benchmark/MathlibQR.json")
    c.add_argument("-k", type=int, default=10)
    c.add_argument("--retrievers", default=",".join(RETRIEVERS))
    c.add_argument("--json", type=Path)
    args = ap.parse_args(argv)
    {"make-queries": make_queries, "run": run, "leansearch": leansearch}[args.cmd](args)


if __name__ == "__main__":
    main()
