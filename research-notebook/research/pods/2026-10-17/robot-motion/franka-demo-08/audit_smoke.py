"""Independent numerical identities and causal negative controls for the smoke harness."""
from pathlib import Path
import hashlib
import json

import numpy as np
from scipy.stats import irwinhall
from run_smoke import ReferenceHistory, box_step

HERE = Path(__file__).resolve().parent


def main():
    config = json.loads((HERE / "protocol.json").read_text())
    frozen = json.loads((HERE / "pre-run-freeze.json").read_text())
    for path, sha in frozen["files"].items():
        assert hashlib.sha256((HERE / path).read_bytes()).hexdigest() == sha, path
    # An independently implemented distribution gives the integrated four boxes.
    points = np.unique(np.r_[np.linspace(-1, 5, 601), 0, 1, 2, 3, 4])
    values = np.array([box_step(z) for z in points])
    scipy_values = irwinhall(4).cdf(points)
    err = float(np.max(abs(values - scipy_values)))
    assert err < 2e-14
    assert np.min(np.diff(values)) >= -2e-14
    assert box_step(2) == 0.5
    history = ReferenceHistory(config["h_s"])
    packets = config["cases"]["queued_reversal"]
    history.receive(packets[0], packets[0]["arrival_ns"])
    prefix_times = range(0, packets[1]["execute_ns"] + 1, 1000000)
    prefix = np.array([history.at(t) for t in prefix_times])
    history.receive(packets[1], packets[1]["arrival_ns"])
    assert np.array_equal(prefix, np.array([history.at(t) for t in prefix_times]))
    assert abs(history.at(2000000000)[0] - packets[-1]["target_rad"]) < 1e-15
    rejected = []
    invalid = [
        ("before_arrival", packets[0], packets[0]["arrival_ns"] - 1),
        ("after_execution", packets[0], packets[0]["execute_ns"] + 1),
        ("arrival_before_issue", dict(packets[0], issue_ns=230000000), 220000000),
    ]
    for name, packet, now in invalid:
        try:
            ReferenceHistory(.2).receive(packet, now)
        except ValueError:
            rejected.append(name)
        else:
            raise AssertionError(name)
    try:
        history.receive(packets[1], packets[1]["arrival_ns"])
    except ValueError:
        rejected.append("duplicate_epoch")
    else:
        raise AssertionError("duplicate_epoch")
    results = json.loads((HERE / "results/summary.json").read_text())
    assert len(results["runs"]) == 16
    for r in results["runs"]:
        tag = f'{r["case"]}__{r["servo"]}__{round(r["integration_dt_s"]*1e6)}us'
        data = np.genfromtxt(HERE / f"results/{tag}.csv", delimiter=",", names=True)
        t = data["time_s"]
        assert len(t) == 2001 and t[0] == 0 and t[-1] == 2
        assert np.max(abs(np.diff(t)-.001)) < 1e-12
        actual = np.stack([data[f"actual_flange_m_{a}"] for a in "xyz"], axis=1)
        goal = np.stack([data[f"goal_flange_m_{a}"] for a in "xyz"], axis=1)
        errors = np.sqrt(np.sum((actual-goal)**2, axis=1))
        tailmax = float(errors[t >= 1.8].max())
        assert abs(tailmax-r["final_window_max_goal_flange_error_m"]) < 1e-14
        assert bool(tailmax <= .0002) == r["final_window_position_pass"]
    report = {"scope": "Coordinator checks; independent identities and CSV score recomputation, not independent plant replay or Lean verification",
        "pre_run_sources_unchanged": True, "scipy_irwinhall_max_error": err,
        "committed_reference_prefix_unchanged": True, "negative_controls_rejected": rejected,
        "csv_runs_rechecked": 16, "all_smoke_pass": all(r["smoke_pass"] for r in results["runs"]),
        "contacts_max": max(r["max_contacts"] for r in results["runs"]),
        "position_passes": sum(r["final_window_position_pass"] for r in results["runs"]),
        "not_hardware_acceptance": True}
    (HERE / "audit.json").write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
