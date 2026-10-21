"""File-backed campaign bookkeeping; not part of the public ctrl CLI."""

from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
from datetime import UTC, datetime
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def now() -> str:
    return datetime.now(UTC).isoformat()


def seconds(a: str, b: str) -> float:
    return (datetime.fromisoformat(b) - datetime.fromisoformat(a)).total_seconds()


def read(name: str):
    return json.loads((ROOT / name).read_text())


def write(name: str, value) -> None:
    path = ROOT / name
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def roster_hash() -> str:
    return hashlib.sha256((ROOT / "roster.json").read_bytes()).hexdigest()


def event(state: dict, message: str) -> None:
    entry = {"at": now(), "problem": state.get("current"), "message": message}
    with (ROOT / "activity.jsonl").open("a") as stream:
        stream.write(json.dumps(entry) + "\n")
    state["last_activity_at"] = entry["at"]


def render(state: dict) -> None:
    rows = read("roster.json")
    lines = [
        "# Crossover campaign — decision board",
        "",
        "AI-written. Pending entries have not received a timed review.",
        "Selection score is a rubric judgment, not a probability of success.",
        "",
        "| Order | ID | Field | Question | Selection /100 | Review | PM gate | Quality /100 |",
        "| --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in rows:
        result = state["problems"][row["id"]]
        title = row["title"].replace("|", "/")
        card = f"[{'★ ' if row['wildcard'] else ''}{title}](cards/{row['id']}/CARD.md)"
        lines.append(
            f"| {row['order']} | {row['id']} | {row['domain']} | {card} | "
            f"{row['selection_score']} | {result['status']} | "
            f"{result.get('decision', '—')} | {result.get('quality', '—')} |"
        )
    completed = sum(p["status"] == "reviewed" for p in state["problems"].values())
    lines.extend(["", f"Completed ten-minute reviews: **{completed}/60**.", ""])
    (ROOT / "DECISION-BOARD.md").write_text("\n".join(lines))


def initialize() -> None:
    if (ROOT / "state.json").exists():
        raise ValueError("state already exists; never reset progress")
    rows = read("roster.json")
    assert len(rows) == 60 and len({r["id"] for r in rows}) == 60
    assert sum(bool(r["wildcard"]) for r in rows) == 10
    for row in rows:
        assert row["source_paths"] and all(Path(p).exists() for p in row["source_paths"])
        directory = ROOT / "cards" / row["id"]
        directory.mkdir(parents=True, exist_ok=True)
        sources = "\n".join(f"- {p}" for p in row["source_paths"])
        (directory / "CARD.md").write_text(
            f"# {row['id']}: {row['title']}\n\n"
            "**NOT REVIEWED — inventory card only.**\n\n"
            f"Question: {row['question']}\n\n"
            f"Prior work ({row['reading_depth']}): {row['prior_work']}\n\n"
            f"Obstacle: {row['obstacle']}\n\n"
            f"Candidate crossover: {row['crossover_seed']}\n\n"
            f"Proposed cheap test: {row['cheap_test']}\n\n"
            f"Selection reason: {row['selection_reason']}\n\nSources:\n\n{sources}\n"
        )
    state = {
        "schema_version": 1,
        "created_at": now(),
        "phase": "breadth",
        "roster_sha256": roster_hash(),
        "current": None,
        "active_segment_started_at": None,
        "last_activity_at": None,
        "automation_id": None,
        "problems": {
            r["id"]: {"status": "pending", "active_seconds": 0, "segments": []} for r in rows
        },
    }
    event(state, "Roster frozen; inventory time excluded from all research sessions")
    write("state.json", state)
    render(state)


def run(args) -> None:
    if args.command == "init":
        initialize()
        return
    state = read("state.json")
    assert state["roster_sha256"] == roster_hash(), "Frozen roster changed"
    if args.command == "render":
        render(state)
        return
    if args.command == "start":
        assert state["current"] is None, "another session is active"
        problem = state["problems"][args.value]
        assert problem["status"] in {"pending", "interrupted"}
        state["current"] = args.value
        state["active_segment_started_at"] = now()
        problem["status"] = "in_progress"
        event(state, "Research starts/resumes after all role assignments: " + args.note)
    elif args.command == "mark":
        assert state["current"], "no active research"
        event(state, args.value)
    elif args.command in {"pause", "finish"}:
        current = state["current"]
        assert current, "no active research"
        problem = state["problems"][current]
        end = now()
        assert seconds(state["last_activity_at"], end) <= 120, (
            "Unexplained inactivity; conservatively close at last_activity_at manually"
        )
        duration = seconds(state["active_segment_started_at"], end)
        total = problem["active_seconds"] + duration
        if args.command == "finish":
            assert total >= 600, "Ten substantive elapsed minutes required"
            directory = ROOT / "cards" / current
            for role in ("domain", "inventor", "critic"):
                assert (directory / f"{role}.md").is_file(), f"Missing {role} evidence"
            decision = json.loads((directory / "decision.json").read_text())
            assert decision["decision"] in {"GO", "HOLD", "NO-GO"}
            assert decision["next_action"] and decision["evidence"]
            assert "NOT REVIEWED" not in (directory / "CARD.md").read_text()
            assert 0 <= decision["quality"] <= 100
            problem.update(decision)
            problem["status"] = "reviewed"
        else:
            problem["status"] = "interrupted"
        problem["segments"].append(
            {"start": state["active_segment_started_at"], "end": end, "seconds": duration}
        )
        problem["active_seconds"] = total
        event(state, args.command + ": " + (args.value or ""))
        state["current"] = None
        state["active_segment_started_at"] = None
    write("state.json", state)
    render(state)
    print(json.dumps({"phase": state["phase"], "current": state["current"]}))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("init", "start", "mark", "pause", "finish", "render"))
    parser.add_argument("value", nargs="?")
    parser.add_argument("--note", default="")
    arguments = parser.parse_args()
    with (ROOT / ".bookkeeping.lock").open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        run(arguments)
