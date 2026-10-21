"""Fresh-clock SQLite tail overrun under a controlled reader; no WCET claim."""

from pathlib import Path
from threading import Event, Thread
import json
import sqlite3
import tempfile
import time

P = Path(__file__).resolve().parent
source = (P / "critic_sqlite_snapshot.py").read_text()
ns = {"__file__": str(P / "critic_sqlite_snapshot.py")}
# Only load unchanged declarations, not producer's top-level experiment loop.
exec(compile(source.split("results=[]")[0], str(P / "critic_sqlite_snapshot.py"), "exec"), ns)
read = Event()
result = {}
with tempfile.TemporaryDirectory(prefix="r03-critic-tail-") as td:
    path = Path(td) / "tail.db"
    ns["setup"](path)
    reader = sqlite3.connect(path, isolation_level=None)
    reader.execute("BEGIN")
    reader.execute("SELECT body FROM live").fetchone()

    def fresh_clock():
        result["clock_wall"] = time.monotonic()
        read.set()
        return ns["F"](1, 2)

    def writer():
        result["status"] = ns["publish"](path, ns["encode"](ns["BASE"]), "tail", fresh_clock)
        result["published_wall"] = time.monotonic()

    thread = Thread(target=writer)
    thread.start()
    assert read.wait(5), "writer did not acquire IMMEDIATE lock/read clock"
    # Keep a legitimate reader open after the fresh clock read. This deliberately
    # exceeds the proposed .01 publication-tail budget and .10 execution margin.
    Event().wait(0.12)
    reader.execute("ROLLBACK")
    reader.close()
    thread.join(5)
    assert not thread.is_alive() and result["status"] == "published"
    elapsed = result["published_wall"] - result["clock_wall"]
    assert elapsed > 0.1
    mapped_return = 0.5 + elapsed
    assert mapped_return > 0.6
out = {
    "status": result["status"],
    "fresh_clock_upper": 0.5,
    "assumed_publication_tail": 0.01,
    "execution_lower": 0.6,
    "measured_read_to_return_seconds": elapsed,
    "mapped_return_time": mapped_return,
    "scope": "Controlled read transaction delayed actual local COMMIT return past a hypothetical deadline despite fresh model clock. This demonstrates absence of a measured .01 tail guarantee; it does not refute ordering theorem when truthful bounded-tail premise holds, nor establish generic SQLite worst-case time.",
}
(P / "critic_commit_tail.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out))
