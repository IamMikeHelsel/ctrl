"""Malformed search certificates must not become evidence of unsatisfiability."""

import copy
import runpy

import pytest
from conftest import REAL

RESEARCH = runpy.run_path(str(REAL / "experiments/crossover.py"))
SOURCE = RESEARCH["SOURCE"]
check_tree = RESEARCH["check_tree"]
read_edges = RESEARCH["read_edges"]
run = RESEARCH["run"]


@pytest.fixture(scope="module")
def evidence():
    return run()


def test_actual_witness_binding_and_certificates(evidence):
    assert evidence["edges"] == read_edges(SOURCE.read_text())
    assert evidence["contradiction_leaves"] == 4
    assert evidence["propagation_certificate"]["branch_nodes"] == 3
    assert evidence["maximum_weighted_cut"] == 42
    assert len(evidence["unique_violation_witnesses"]) == 22
    assert evidence["clique_cover_relaxation"]["exact_dual_objective"] == "44"


def test_checker_rejects_wrong_forced_color(evidence):
    certificate = copy.deepcopy(evidence["propagation_certificate"])
    certificate["tree"]["children"][0]["forced"][0][1] ^= 1
    with pytest.raises(ValueError, match="antecedents"):
        check_tree(evidence["edges"], certificate)


def test_checker_rejects_missing_branch(evidence):
    certificate = copy.deepcopy(evidence["propagation_certificate"])
    certificate["tree"]["children"].pop()
    with pytest.raises(ValueError, match="both children"):
        check_tree(evidence["edges"], certificate)


def test_checker_rejects_false_conflict(evidence):
    certificate = copy.deepcopy(evidence["propagation_certificate"])
    certificate["tree"] = {"forced": [], "conflict": 0}
    with pytest.raises(ValueError, match="not monochromatic"):
        check_tree(evidence["edges"], certificate)


def test_witness_parser_rejects_expressions():
    with pytest.raises(ValueError, match="unexpected token"):
        read_edges(SOURCE.read_text().replace("{0, 1, 2}", "{0, 1, 1+1}", 1))
