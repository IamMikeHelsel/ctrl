"""
Synergy lens: a weighted cross-domain unlock graph over ctrl ideas and
research candidates.

Data sources
  docs/AGENT_IDEA_INDEX.json   existing idea nodes (CTRL-01 ... MATH-04)
  docs/SYNERGY_WEIGHTS.json    domains, domain->domain weights, typed idea
                               edges, research candidates, scoring recipe

Subcommands (see `ctrl synergy -h`)
  matrix    domain x domain unlock weights (ASCII heatmap or JSON)
  unlock    what an idea unlocks and what unlocks it (1- and 2-hop)
  rank      rank ideas/candidates by the scoring recipe, optionally by goal
  next      top-N candidates to pick up next, with a weeks budget
  gaps      strong domain pairs with no concrete idea edge yet
  path      best weighted chain from one idea to another
  validate  schema and referential-integrity check

Everything is stdlib-only so it runs in CI and inside agents.
"""

from __future__ import annotations

import heapq
import json
import math
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Tuple

NOVELTY = {"N1": 1, "N2": 2, "N3": 3}
APPLICABILITY = {"A1": 1, "A2": 2, "A3": 3}
STOPWORDS = {
    "the", "a", "an", "and", "or", "of", "for", "to", "in", "on", "with",
    "via", "by", "from", "as", "at", "is", "are", "be", "that", "this",
    "into", "over", "under", "without", "plus", "its", "than", "then",
}


@dataclass
class Node:
    id: str
    title: str
    kind: str  # idea | candidate
    status: str
    domains: List[str]
    novelty: int = 2
    applicability: int = 2
    payoff: float = 3.0
    effort_weeks: float = 4.0
    confidence: float = 1.0
    external_pull: str = ""
    text: str = ""
    raw: dict = field(default_factory=dict)


@dataclass
class Edge:
    src: str
    dst: str
    weight: float
    etype: str = "composes"
    why: str = ""


class SynergyGraph:
    def __init__(self, index: dict, weights: dict):
        self.index = index
        self.weights = weights
        self.domains: Dict[str, dict] = weights.get("domains", {})
        self.nodes: Dict[str, Node] = {}
        self.edges: List[Edge] = []
        self.domain_edges: Dict[Tuple[str, str], dict] = {}
        self._load()

    # ------------------------------------------------------------------ load
    def _load(self) -> None:
        idea_domains = self.weights.get("idea_domains", {})
        for idea in self.index.get("ideas", []):
            iid = idea["id"]
            text = " ".join(
                [
                    idea.get("title", ""),
                    idea.get("domain", ""),
                    idea.get("approach", ""),
                    " ".join(idea.get("key_theorems", [])),
                    " ".join(idea.get("lean_modules", [])),
                ]
            )
            self.nodes[iid] = Node(
                id=iid,
                title=idea.get("title", iid),
                kind="idea",
                status=idea.get("status", "ready_to_use"),
                domains=list(idea_domains.get(iid, [])),
                novelty=NOVELTY.get(idea.get("novelty", "N2"), 2),
                applicability=APPLICABILITY.get(idea.get("applicability", "A2"), 2),
                payoff=3.0 + (1.0 if idea.get("measured_impact") else 0.0),
                effort_weeks=0.0,
                confidence=1.0,
                external_pull=idea.get("external_pull", ""),
                text=text,
                raw=idea,
            )
        for cand in self.weights.get("candidates", []):
            cid = cand["id"]
            text = " ".join(
                [
                    cand.get("title", ""),
                    " ".join(cand.get("domains", [])),
                    cand.get("why_now", ""),
                    cand.get("missing_capability", ""),
                    cand.get("external_pull", ""),
                    cand.get("kind", ""),
                ]
            )
            nov = cand.get("novelty")
            app = cand.get("applicability")
            self.nodes[cid] = Node(
                id=cid,
                title=cand.get("title", cid),
                kind="candidate",
                status=cand.get("status", "candidate"),
                domains=list(cand.get("domains", [])),
                novelty=NOVELTY.get(nov, _kind_novelty(cand.get("kind", "explore"))),
                applicability=APPLICABILITY.get(app, _kind_applicability(cand.get("kind", "explore"))),
                payoff=float(cand.get("payoff", 3)),
                effort_weeks=float(cand.get("effort_weeks", 4)),
                confidence=float(cand.get("confidence", 0.5)),
                external_pull=cand.get("external_pull", ""),
                text=text,
                raw=cand,
            )
        # Explicit typed idea edges.
        for e in self.weights.get("idea_edges", []):
            self.edges.append(Edge(e["from"], e["to"], float(e["weight"]), e.get("type", "composes"), e.get("why", "")))
        explicit = {(e.src, e.dst) for e in self.edges}
        # Implicit edges from the index's combines_with lists (symmetric, weaker).
        for idea in self.index.get("ideas", []):
            for other in idea.get("combines_with", []):
                for a, b in ((idea["id"], other), (other, idea["id"])):
                    if (a, b) not in explicit and a in self.nodes and b in self.nodes:
                        self.edges.append(Edge(a, b, 0.4, "composes", "listed in combines_with"))
                        explicit.add((a, b))
        # Candidate edges: builds_on (X -> cand, type feeds) and unlocks (cand -> Y).
        for cand in self.weights.get("candidates", []):
            cid = cand["id"]
            for src in cand.get("builds_on", []):
                if src in self.nodes and (src, cid) not in explicit:
                    self.edges.append(Edge(src, cid, 0.7, "feeds", "candidate builds on this idea"))
                    explicit.add((src, cid))
            for dst in cand.get("unlocks", []):
                if dst in self.nodes and (cid, dst) not in explicit:
                    self.edges.append(Edge(cid, dst, 0.6, "enables", "candidate unlocks this idea"))
                    explicit.add((cid, dst))
        for de in self.weights.get("domain_edges", []):
            self.domain_edges[(de["from"], de["to"])] = de

    # --------------------------------------------------------------- helpers
    def out_edges(self, nid: str) -> List[Edge]:
        return [e for e in self.edges if e.src == nid]

    def in_edges(self, nid: str) -> List[Edge]:
        return [e for e in self.edges if e.dst == nid]

    def domain_weight(self, a: str, b: str) -> float:
        if a == b:
            return 1.0
        de = self.domain_edges.get((a, b))
        return float(de["weight"]) if de else 0.0

    def unlock_in(self, nid: str, ready_only: bool = True) -> float:
        total = 0.0
        for e in self.in_edges(nid):
            src = self.nodes.get(e.src)
            if src is None:
                continue
            if ready_only and src.status != "ready_to_use":
                continue
            total += e.weight
        return total

    def builds_on_readiness(self, nid: str) -> float:
        """Mean readiness of the ideas a candidate builds on (SED counts 0.8)."""
        sc = self.weights.get("scoring", {}).get("readiness", {})
        refs = self.nodes[nid].raw.get("builds_on", [])
        if not refs:
            return 0.5
        vals = []
        for r in refs:
            if r == "SED":
                vals.append(0.8)
            elif r in self.nodes:
                vals.append(sc.get(self.nodes[r].status, 0.6))
        return sum(vals) / len(vals) if vals else 0.5

    def unlock_out(self, nid: str) -> float:
        return sum(e.weight for e in self.out_edges(nid))

    def domain_affinity(self, nid: str, domains: Iterable[str]) -> float:
        """Max domain->domain weight from the node's domains to the target domains."""
        targets = list(domains)
        if not targets:
            return 1.0
        node = self.nodes[nid]
        best = 0.0
        for a in node.domains or [""]:
            for b in targets:
                best = max(best, self.domain_weight(a, b))
        return best

    # --------------------------------------------------------------- scoring
    def score(self, nid: str, goal: Optional[str] = None, target_domains: Iterable[str] = ()) -> dict:
        sc = self.weights.get("scoring", {})
        c = sc.get("coefficients", {})
        readiness = sc.get("readiness", {})
        n = self.nodes[nid]
        # Soft saturation: 1.5 total incoming weight -> 0.76, 3.0 -> 0.96.
        uin = math.tanh(self.unlock_in(nid) / 1.5)
        uout = math.tanh(self.unlock_out(nid) / 1.5)
        pull = pull_tier(n.external_pull)
        base = (
            c.get("w_nov", 0.15) * n.novelty / 3.0
            + c.get("w_app", 0.15) * n.applicability / 3.0
            + c.get("w_pay", 0.25) * n.payoff / 5.0
            + c.get("w_unlock", 0.2) * uin
            + c.get("w_out", 0.1) * uout
            + c.get("w_pull", 0.1) * pull
        )
        effort_pen = c.get("w_eff", 0.15) * math.log1p(max(0.0, n.effort_weeks)) / math.log1p(26.0)
        ready_mult = readiness.get(n.status, 0.6)
        if n.kind == "candidate":
            # a candidate inherits readiness from what it builds on (XD scout rule)
            ready_mult = 0.6 + 0.4 * self.builds_on_readiness(nid)
        value = n.confidence * ready_mult * base - effort_pen
        rel = 1.0
        if goal:
            rel = 0.25 + 0.75 * goal_relevance(goal, n.text)
        aff = self.domain_affinity(nid, target_domains)
        if target_domains:
            rel *= 0.25 + 0.75 * aff
        return {
            "id": nid,
            "score": round(value * rel, 4),
            "base": round(value, 4),
            "relevance": round(rel, 3),
            "unlock_in": round(uin, 3),
            "unlock_out": round(uout, 3),
            "effort_weeks": n.effort_weeks,
            "confidence": n.confidence,
            "status": n.status,
            "kind": n.kind,
        }

    def rank(self, goal: Optional[str] = None, kinds: Iterable[str] = (), domains: Iterable[str] = (),
             cand_kind: Optional[str] = None, limit: int = 0) -> List[dict]:
        kinds = set(kinds)
        rows = []
        for nid, n in self.nodes.items():
            if kinds and n.kind not in kinds:
                continue
            if cand_kind and n.raw.get("kind") != cand_kind:
                continue
            r = self.score(nid, goal, domains)
            r["title"] = n.title
            r["domains"] = n.domains
            r["candidate_kind"] = n.raw.get("kind", "")
            rows.append(r)
        rows.sort(key=lambda r: (-r["score"], r["id"]))
        return rows[:limit] if limit else rows

    def next_plan(self, budget_weeks: float, goal: Optional[str] = None, domains: Iterable[str] = ()) -> List[dict]:
        """Greedy knapsack by score-per-week on candidates only."""
        rows = [r for r in self.rank(goal, kinds=("candidate",), domains=domains) if r["effort_weeks"] > 0]
        rows.sort(key=lambda r: -(r["score"] / r["effort_weeks"]))
        plan, used = [], 0.0
        for r in rows:
            if used + r["effort_weeks"] <= budget_weeks:
                plan.append(r)
                used += r["effort_weeks"]
        return plan

    # ----------------------------------------------------------------- graph
    def unlock(self, nid: str, hops: int = 2) -> dict:
        if nid not in self.nodes:
            raise KeyError(nid)
        out1 = sorted(self.out_edges(nid), key=lambda e: -e.weight)
        in1 = sorted(self.in_edges(nid), key=lambda e: -e.weight)
        reach: Dict[str, float] = {}
        if hops >= 2:
            for e in out1:
                for e2 in self.out_edges(e.dst):
                    if e2.dst in (nid,) or e2.dst in {x.dst for x in out1}:
                        continue
                    w = e.weight * e2.weight
                    if w > reach.get(e2.dst, 0.0):
                        reach[e2.dst] = w
        return {
            "id": nid,
            "title": self.nodes[nid].title,
            "unlocks": [_edge_dict(e, self.nodes) for e in out1],
            "unlocked_by": [_edge_dict(e, self.nodes) for e in in1],
            "two_hop": sorted(
                ({"id": k, "title": self.nodes[k].title, "weight": round(v, 3)} for k, v in reach.items()),
                key=lambda d: -d["weight"],
            ),
        }

    def path(self, src: str, dst: str) -> Optional[dict]:
        """Max-product path via Dijkstra on -log(weight)."""
        if src not in self.nodes or dst not in self.nodes:
            raise KeyError(f"{src} or {dst}")
        dist = {src: 0.0}
        prev: Dict[str, Tuple[str, Edge]] = {}
        pq = [(0.0, src)]
        while pq:
            d, u = heapq.heappop(pq)
            if u == dst:
                break
            if d > dist.get(u, math.inf):
                continue
            for e in self.out_edges(u):
                nd = d - math.log(max(e.weight, 1e-9))
                if nd < dist.get(e.dst, math.inf):
                    dist[e.dst] = nd
                    prev[e.dst] = (u, e)
                    heapq.heappush(pq, (nd, e.dst))
        if dst not in dist:
            return None
        chain, cur = [], dst
        while cur != src:
            u, e = prev[cur]
            chain.append(_edge_dict(e, self.nodes))
            cur = u
        chain.reverse()
        return {"from": src, "to": dst, "strength": round(math.exp(-dist[dst]), 4), "chain": chain}

    def gaps(self, min_weight: float = 0.5) -> List[dict]:
        """Domain pairs with a strong domain edge but no idea-level edge crossing them."""
        covered: Dict[Tuple[str, str], int] = {}
        for e in self.edges:
            a, b = self.nodes.get(e.src), self.nodes.get(e.dst)
            if not a or not b:
                continue
            for da in a.domains:
                for db in b.domains:
                    if da != db:
                        covered[(da, db)] = covered.get((da, db), 0) + 1
        out = []
        for (da, db), de in self.domain_edges.items():
            if float(de["weight"]) >= min_weight:
                n = covered.get((da, db), 0)
                out.append({"from": da, "to": db, "weight": de["weight"], "idea_edges": n, "why": de.get("why", "")})
        out.sort(key=lambda g: (g["idea_edges"], -g["weight"]))
        return out

    def matrix(self) -> dict:
        keys = list(self.domains.keys())
        return {
            "domains": keys,
            "rows": [[self.domain_weight(a, b) if a != b else None for b in keys] for a in keys],
        }

    # -------------------------------------------------------------- validate
    def validate(self) -> List[str]:
        problems = []
        ids = set(self.nodes)
        dom = set(self.domains)
        seen = set()
        for idea in self.index.get("ideas", []):
            if idea["id"] in seen:
                problems.append(f"duplicate idea id {idea['id']}")
            seen.add(idea["id"])
        for cand in self.weights.get("candidates", []):
            if cand["id"] in seen:
                problems.append(f"duplicate candidate id {cand['id']}")
            seen.add(cand["id"])
            for k in ("title", "kind", "domains", "effort_weeks", "payoff", "confidence"):
                if k not in cand:
                    problems.append(f"{cand['id']} missing field {k}")
            if cand.get("kind") not in ("explore", "productionize", "industrialize"):
                problems.append(f"{cand['id']} bad kind {cand.get('kind')}")
            for d in cand.get("domains", []):
                if d not in dom:
                    problems.append(f"{cand['id']} unknown domain {d}")
            for ref in cand.get("builds_on", []) + cand.get("unlocks", []):
                if ref not in ids and ref != "SED":
                    problems.append(f"{cand['id']} references unknown id {ref}")
            if not (0.0 <= float(cand.get("confidence", 0)) <= 1.0):
                problems.append(f"{cand['id']} confidence out of range")
        for e in self.weights.get("idea_edges", []):
            if e["from"] not in ids or e["to"] not in ids:
                problems.append(f"idea edge {e['from']}->{e['to']} references unknown id")
            if not (0.0 <= float(e["weight"]) <= 1.0):
                problems.append(f"idea edge {e['from']}->{e['to']} weight out of range")
        for de in self.weights.get("domain_edges", []):
            if de["from"] not in dom or de["to"] not in dom:
                problems.append(f"domain edge {de['from']}->{de['to']} unknown domain")
            if not (0.0 <= float(de["weight"]) <= 1.0):
                problems.append(f"domain edge {de['from']}->{de['to']} weight out of range")
        for iid, ds in self.weights.get("idea_domains", {}).items():
            if iid not in ids:
                problems.append(f"idea_domains names unknown idea {iid}")
            for d in ds:
                if d not in dom:
                    problems.append(f"idea_domains[{iid}] unknown domain {d}")
        for n in self.nodes.values():
            if n.kind == "idea" and not n.domains:
                problems.append(f"idea {n.id} has no domain tag in idea_domains")
        return problems


# ---------------------------------------------------------------- utilities
def _kind_novelty(kind: str) -> int:
    return {"explore": 3, "productionize": 2, "industrialize": 1}.get(kind, 2)


def _kind_applicability(kind: str) -> int:
    return {"explore": 1, "productionize": 2, "industrialize": 3}.get(kind, 2)


def _edge_dict(e: Edge, nodes: Dict[str, Node]) -> dict:
    return {
        "from": e.src,
        "to": e.dst,
        "weight": e.weight,
        "type": e.etype,
        "why": e.why,
        "from_title": nodes[e.src].title if e.src in nodes else "",
        "to_title": nodes[e.dst].title if e.dst in nodes else "",
    }


PULL_STRONG = ("bounty", "prize", "customer", "contract", "grant", "fund", "revenue", "paying", "market")
PULL_STANDARD = ("standard", "certif", "iso ", "iso/", "iec ", "do-178", "do-333", "regulat", "passport", "fda", "sil ", "asil")


def pull_tier(text: str) -> float:
    """1.0 money/customer, 0.7 standard/certification, 0.4 community, 0 none."""
    t = (text or "").lower().strip()
    if not t or t in ("none", "n/a", "-"):
        return 0.0
    if any(k in t for k in PULL_STRONG):
        return 1.0
    if any(k in t for k in PULL_STANDARD):
        return 0.7
    return 0.4


def tokens(text: str) -> List[str]:
    return [t for t in re.findall(r"[a-z0-9][a-z0-9\-]+", text.lower()) if t not in STOPWORDS and len(t) > 2]


def goal_relevance(goal: str, text: str) -> float:
    g = set(tokens(goal))
    if not g:
        return 1.0
    t = set(tokens(text))
    hits = sum(1 for w in g if w in t or any(x.startswith(w[:5]) for x in t if len(w) >= 5))
    return hits / len(g)


def load_graph(repo_root: Path) -> SynergyGraph:
    index_path = repo_root / "docs" / "AGENT_IDEA_INDEX.json"
    weights_path = repo_root / "docs" / "SYNERGY_WEIGHTS.json"
    with open(index_path) as f:
        index = json.load(f)
    with open(weights_path) as f:
        weights = json.load(f)
    return SynergyGraph(index, weights)


# ----------------------------------------------------------------------- CLI
def _bar(w: Optional[float]) -> str:
    if w is None:
        return "  ·  "
    if w <= 0:
        return "  .  "
    blocks = " ▁▂▃▄▅▆▇█"
    return f" {blocks[min(8, int(round(w * 8)))]}{w:.1f}"


def run_synergy_cli(args, repo_root: Path) -> int:
    try:  # let `| head` close the pipe quietly
        import signal

        signal.signal(signal.SIGPIPE, signal.SIG_DFL)
    except (AttributeError, ValueError):
        pass
    g = load_graph(repo_root)
    cmd = args.synergy_cmd
    as_json = getattr(args, "json", False)

    if cmd == "validate":
        problems = g.validate()
        if as_json:
            print(json.dumps({"ok": not problems, "problems": problems}, indent=2))
        else:
            if problems:
                for p in problems:
                    print(f"  ✗ {p}")
                print(f"\n{len(problems)} problem(s)")
            else:
                print(f"ok: {len(g.nodes)} nodes, {len(g.edges)} idea edges, {len(g.domain_edges)} domain edges")
        return 1 if problems else 0

    if cmd == "matrix":
        m = g.matrix()
        if as_json:
            print(json.dumps(m, indent=2))
            return 0
        keys = m["domains"]
        short = [k[:6] for k in keys]
        print("rows unlock columns  (weight 0-1)\n")
        print(" " * 22 + "".join(f"{s:>7}" for s in short))
        for a, row in zip(keys, m["rows"]):
            print(f"{a:>22}" + "".join(f"{_bar(w):>7}" for w in row))
        return 0

    if cmd == "unlock":
        try:
            u = g.unlock(args.id, hops=2)
        except KeyError:
            print(f"unknown id {args.id}")
            return 2
        if as_json:
            print(json.dumps(u, indent=2))
            return 0
        print(f"{u['id']}  {u['title']}\n")
        print("unlocks:")
        for e in u["unlocks"]:
            print(f"  {e['weight']:.2f} {e['type']:<13} → {e['to']:<9} {e['to_title'][:60]}")
        print("unlocked by:")
        for e in u["unlocked_by"]:
            print(f"  {e['weight']:.2f} {e['type']:<13} ← {e['from']:<9} {e['from_title'][:60]}")
        if u["two_hop"]:
            print("two hops away:")
            for r in u["two_hop"][:8]:
                print(f"  {r['weight']:.2f} → {r['id']:<9} {r['title'][:60]}")
        return 0

    if cmd in ("rank", "next"):
        domains = [d for d in (args.domain or "").split(",") if d]
        for d in domains:
            if d not in g.domains:
                print(f"unknown domain {d}; known: {', '.join(g.domains)}")
                return 2
        if cmd == "rank":
            kinds = () if args.all else ("candidate",) if args.candidates else ()
            rows = g.rank(args.goal, kinds=kinds, domains=domains, cand_kind=args.kind, limit=args.limit)
        else:
            rows = g.next_plan(args.budget, args.goal, domains)
        if as_json:
            print(json.dumps(rows, indent=2))
            return 0
        hdr = f"{'score':>6} {'base':>6} {'rel':>5} {'in':>4} {'wk':>4} {'conf':>4}  id         title"
        print(hdr)
        for r in rows:
            print(
                f"{r['score']:6.3f} {r['base']:6.3f} {r['relevance']:5.2f} {r['unlock_in']:4.2f} "
                f"{r['effort_weeks']:4.0f} {r['confidence']:4.2f}  {r['id']:<10} "
                f"[{(r.get('candidate_kind') or r['kind'])[:4]}] {r['title'][:70]}"
            )
        if cmd == "next":
            used = sum(r["effort_weeks"] for r in rows)
            print(f"\n{len(rows)} items, {used:.0f} of {args.budget:.0f} weeks")
        return 0

    if cmd == "gaps":
        rows = g.gaps(args.min_weight)
        if as_json:
            print(json.dumps(rows, indent=2))
            return 0
        print("strong domain edges ranked by how few concrete idea edges cross them\n")
        for r in rows:
            flag = "GAP " if r["idea_edges"] == 0 else "    "
            print(f"{flag}{r['weight']:.1f} {r['from']:>22} → {r['to']:<22} {r['idea_edges']:>2} idea edge(s)  {r['why'][:70]}")
        return 0

    if cmd == "path":
        try:
            p = g.path(args.src, args.dst)
        except KeyError as e:
            print(f"unknown id {e}")
            return 2
        if p is None:
            print(f"no path from {args.src} to {args.dst}")
            return 1
        if as_json:
            print(json.dumps(p, indent=2))
            return 0
        print(f"{p['from']} → {p['to']}  strength {p['strength']:.3f}")
        for e in p["chain"]:
            print(f"  {e['from']:<9} —{e['type']} {e['weight']:.2f}→ {e['to']:<9} {e['why'][:70]}")
        return 0

    print("no synergy subcommand given; try `ctrl synergy -h`")
    return 2


def add_synergy_parser(subparsers) -> None:
    p = subparsers.add_parser(
        "synergy",
        help="Cross-domain unlock graph: what unlocks what, ranked next steps, gaps",
    )
    sp = p.add_subparsers(dest="synergy_cmd")

    m = sp.add_parser("matrix", help="Domain x domain unlock weights")
    m.add_argument("--json", action="store_true")

    u = sp.add_parser("unlock", help="What an idea unlocks and what unlocks it")
    u.add_argument("id", help="Idea or candidate id, e.g. CTRL-01")
    u.add_argument("--json", action="store_true")

    r = sp.add_parser("rank", help="Rank ideas and candidates by the scoring recipe")
    r.add_argument("-g", "--goal", help="Free-text goal to bias relevance, e.g. 'legged robot safety kernel'")
    r.add_argument("-d", "--domain", help="Comma-separated target domains to bias by domain affinity")
    r.add_argument("-k", "--kind", choices=["explore", "productionize", "industrialize"], help="Only candidates of this kind")
    r.add_argument("-c", "--candidates", action="store_true", help="Only research candidates (exclude existing ideas)")
    r.add_argument("-a", "--all", action="store_true", help="Ideas and candidates (default)")
    r.add_argument("-n", "--limit", type=int, default=0)
    r.add_argument("--json", action="store_true")

    nx = sp.add_parser("next", help="Greedy plan of candidates within a weeks budget")
    nx.add_argument("-b", "--budget", type=float, default=12.0, help="Engineer-weeks available (default 12)")
    nx.add_argument("-g", "--goal")
    nx.add_argument("-d", "--domain")
    nx.add_argument("--json", action="store_true")

    gp = sp.add_parser("gaps", help="Strong domain pairs with no concrete idea edge")
    gp.add_argument("--min-weight", type=float, default=0.5)
    gp.add_argument("--json", action="store_true")

    pa = sp.add_parser("path", help="Best weighted chain from one idea to another")
    pa.add_argument("src")
    pa.add_argument("dst")
    pa.add_argument("--json", action="store_true")

    v = sp.add_parser("validate", help="Schema and referential integrity check")
    v.add_argument("--json", action="store_true")
