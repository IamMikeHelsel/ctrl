"""Unit tests for the synergy lens. Run: python3 -m unittest discover -s tools/tests"""
import json
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))

from ctrl_cli.synergy import SynergyGraph, goal_relevance, load_graph  # noqa: E402


def tiny():
    index = {
        "ideas": [
            {"id": "A-01", "title": "Alpha DARE", "domain": "x", "status": "ready_to_use", "novelty": "N3",
             "applicability": "A3", "approach": "riccati gain", "combines_with": ["B-01"]},
            {"id": "B-01", "title": "Beta Kalman", "domain": "y", "status": "ready_to_use", "novelty": "N2",
             "applicability": "A2", "approach": "filter"},
            {"id": "C-01", "title": "Gamma open", "domain": "z", "status": "in_work", "novelty": "N3",
             "applicability": "A1", "approach": "conjecture"},
        ]
    }
    weights = {
        "domains": {"controls": {}, "estimation": {}, "math": {}},
        "idea_domains": {"A-01": ["controls"], "B-01": ["estimation"], "C-01": ["math"]},
        "domain_edges": [
            {"from": "controls", "to": "estimation", "weight": 0.9, "why": "dual"},
            {"from": "math", "to": "controls", "weight": 0.6, "why": "conditioning"},
        ],
        "idea_edges": [{"from": "A-01", "to": "B-01", "type": "dualizes", "weight": 0.9, "why": "dual"}],
        "scoring": {
            "coefficients": {"w_nov": 0.15, "w_app": 0.15, "w_pay": 0.25, "w_unlock": 0.2, "w_out": 0.1,
                             "w_pull": 0.1, "w_eff": 0.15},
            "readiness": {"ready_to_use": 1.0, "promising_near_complete": 0.85, "in_work": 0.7, "candidate": 0.6},
        },
        "candidates": [
            {"id": "X-01", "title": "Kalman on Lie groups", "kind": "explore", "domains": ["estimation"],
             "builds_on": ["B-01"], "unlocks": ["C-01"], "effort_weeks": 3, "payoff": 4, "confidence": 0.8,
             "external_pull": "customer"},
            {"id": "X-02", "title": "Ship DARE kernel", "kind": "industrialize", "domains": ["controls"],
             "builds_on": ["A-01"], "unlocks": [], "effort_weeks": 20, "payoff": 2, "confidence": 0.5,
             "external_pull": ""},
        ],
    }
    return SynergyGraph(index, weights)


class TinyGraphTests(unittest.TestCase):
    def test_edges_are_built_from_all_sources(self):
        g = tiny()
        pairs = {(e.src, e.dst) for e in g.edges}
        self.assertIn(("A-01", "B-01"), pairs)       # explicit
        self.assertIn(("B-01", "A-01"), pairs)       # combines_with reverse
        self.assertIn(("B-01", "X-01"), pairs)       # builds_on
        self.assertIn(("X-01", "C-01"), pairs)       # unlocks
        explicit = [e for e in g.edges if e.src == "A-01" and e.dst == "B-01"]
        self.assertEqual(len(explicit), 1)
        self.assertEqual(explicit[0].weight, 0.9)

    def test_unlock_in_counts_only_ready_sources(self):
        g = tiny()
        self.assertAlmostEqual(g.unlock_in("X-01"), 0.7)
        self.assertAlmostEqual(g.unlock_in("C-01"), 0.0)  # only a candidate points at it
        self.assertAlmostEqual(g.unlock_in("C-01", ready_only=False), 0.6)

    def test_rank_prefers_cheap_connected_candidate(self):
        g = tiny()
        rows = g.rank(kinds=("candidate",))
        self.assertEqual(rows[0]["id"], "X-01")
        self.assertGreater(rows[0]["score"], rows[1]["score"])

    def test_goal_and_domain_bias(self):
        g = tiny()
        rows = g.rank(goal="kalman filter", kinds=("candidate",))
        self.assertEqual(rows[0]["id"], "X-01")
        self.assertGreater(rows[0]["relevance"], rows[1]["relevance"])
        rows = g.rank(domains=["estimation"], kinds=("idea",))
        self.assertEqual([r["id"] for r in rows[:2]], ["B-01", "A-01"])  # in-domain first, then strongest unlocker
        self.assertEqual(g.domain_affinity("B-01", ["estimation"]), 1.0)
        self.assertAlmostEqual(g.domain_affinity("A-01", ["estimation"]), 0.45)  # 0.5 * 0.9
        self.assertEqual(g.domain_affinity("C-01", ["estimation"]), 0.0)

    def test_next_respects_budget(self):
        g = tiny()
        plan = g.next_plan(budget_weeks=5)
        self.assertEqual([r["id"] for r in plan], ["X-01"])
        plan = g.next_plan(budget_weeks=30, min_score=0.0)
        self.assertEqual(sorted(r["id"] for r in plan), ["X-01", "X-02"])
        plan = g.next_plan(budget_weeks=30, min_score=0.9)
        self.assertEqual(plan, [])

    def test_path_and_unlock(self):
        g = tiny()
        p = g.path("A-01", "C-01")
        self.assertIsNotNone(p)
        self.assertEqual([e["to"] for e in p["chain"]], ["B-01", "X-01", "C-01"])
        self.assertAlmostEqual(p["strength"], 0.9 * 0.7 * 0.6, places=3)
        self.assertIsNone(g.path("C-01", "A-01"))
        u = g.unlock("A-01")
        self.assertEqual(u["unlocks"][0]["to"], "B-01")
        self.assertTrue(any(r["id"] == "X-01" for r in u["two_hop"]))

    def test_gaps_flags_uncrossed_domain_edges(self):
        g = tiny()
        gaps = g.gaps(min_weight=0.5)
        by = {(r["from"], r["to"]): r["idea_edges"] for r in gaps}
        self.assertGreater(by[("controls", "estimation")], 0)
        self.assertEqual(by[("math", "controls")], 0)
        self.assertEqual(gaps[0]["from"], "math")

    def test_validate_catches_bad_refs(self):
        g = tiny()
        self.assertEqual(g.validate(), [])
        g.weights["candidates"].append({"id": "BAD", "title": "t", "kind": "nope", "domains": ["sport"],
                                        "builds_on": ["Q-99"], "effort_weeks": 1, "payoff": 1, "confidence": 2})
        g2 = SynergyGraph(g.index, g.weights)
        msgs = "\n".join(g2.validate())
        for needle in ("bad kind", "unknown domain sport", "unknown id Q-99", "confidence out of range"):
            self.assertIn(needle, msgs)

    def test_goal_relevance(self):
        self.assertEqual(goal_relevance("", "anything"), 1.0)
        self.assertEqual(goal_relevance("kalman filter", "kalman filter"), 1.0)
        self.assertEqual(goal_relevance("kalman filter", "unrelated"), 0.0)


class RepoDataTests(unittest.TestCase):
    def test_repo_data_validates(self):
        g = load_graph(ROOT)
        self.assertEqual(g.validate(), [])
        self.assertGreaterEqual(len(g.nodes), 20)

    def test_site_index_in_sync(self):
        a = json.load(open(ROOT / "docs" / "AGENT_IDEA_INDEX.json"))
        b = json.load(open(ROOT / "site" / "AGENT_IDEA_INDEX.json"))
        self.assertEqual(a, b)


if __name__ == "__main__":
    unittest.main()
