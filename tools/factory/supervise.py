"""Admit one bounded 44 run under the existing cooperative Spark host lock."""

import argparse
import fcntl
import importlib.util
import json
import os
import subprocess
import sys
import time
import urllib.request
from pathlib import Path


def api(path, payload=None):
    req = urllib.request.Request(
        "http://127.0.0.1:11434/api/" + path,
        data=None if payload is None else json.dumps(payload).encode(),
        headers={"Content-Type": "application/json"},
    )
    with urllib.request.urlopen(req, timeout=180) as response:
        return json.load(response)


def preflight(root):
    spec = importlib.util.spec_from_file_location("backend", root / "control/backend.py")
    backend = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(backend)
    probe = root / "build/preflight.lean"
    good = "import Mathlib\ntheorem probe : (2 + 2 : ℕ) = 4 := by norm_num\n#print axioms probe\n"
    results = {}
    for name, text, expected in (
        ("true_statement", good, True),
        ("false_statement", good.replace("= 4", "= 5"), False),
    ):
        probe.write_text(text)
        cp = subprocess.run(
            backend.sandbox(
                ["/toolchain/bin/lean", "/build/preflight.lean"], root, root / "project"
            ),
            capture_output=True,
            text=True,
            timeout=90,
            preexec_fn=backend.limits,
        )
        (root / "build" / f"preflight-{name}.log").write_text(cp.stdout + cp.stderr)
        results[name] = (cp.returncode == 0) == expected
    for index, task in enumerate(json.loads((root / "acceptance/contracts.json").read_text()), 1):
        probe.write_text(
            task["imports"]
            + "\ndef statement : Prop :=\n"
            + task["statement"]
            + "\n#check statement\n"
        )
        cp = subprocess.run(
            backend.sandbox(
                ["/toolchain/bin/lean", "/build/preflight.lean"], root, root / "project"
            ),
            capture_output=True,
            text=True,
            timeout=90,
            preexec_fn=backend.limits,
        )
        (root / "build" / f"preflight-contract-{index}.log").write_text(cp.stdout + cp.stderr)
        results[f"contract_{index}"] = cp.returncode == 0
    isolation = (
        "import pathlib,socket\n"
        "assert not pathlib.Path('/home/mike/.ssh').exists()\n"
        "try:\n pathlib.Path('/acceptance/probe').write_text('x')\n"
        "except OSError: pass\nelse: raise AssertionError('writable acceptance')\n"
        "s=socket.socket(); s.settimeout(1)\n"
        "assert s.connect_ex(('127.0.0.1',11434)) != 0\n"
    )
    cp = subprocess.run(
        backend.sandbox(["/usr/bin/python3", "-c", isolation], root, root / "project"),
        capture_output=True,
        text=True,
        timeout=15,
        preexec_fn=backend.limits,
    )
    results["isolation"] = cp.returncode == 0
    (root / "preflight.json").write_text(json.dumps(results, indent=2) + "\n")
    if not all(results.values()):
        raise RuntimeError(f"Sandbox preflight failed: {results}")
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--model", default="leanstral:latest")
    parser.add_argument("--minutes", type=float, default=20)
    parser.add_argument("--preflight-only", action="store_true")
    args = parser.parse_args()
    if not 0 < args.minutes <= 60 or ":cloud" in args.model:
        raise ValueError("Local model and a finite 0..60 minute budget required")
    root = Path(__file__).resolve().parents[1]
    print(json.dumps(preflight(root)), flush=True)
    if args.preflight_only:
        return
    lockpath = Path.home() / ".local/state/44/donut-host.lock"
    lockpath.parent.mkdir(parents=True, exist_ok=True)
    with lockpath.open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        resident = api("ps")["models"]
        if resident and (len(resident) != 1 or resident[0]["name"] != args.model):
            raise RuntimeError("Another model is resident; no switching or eviction")
        installed = {m["name"]: m for m in api("tags")["models"]}
        if args.model not in installed:
            raise RuntimeError("Model not installed; no downloads")
        for _ in range(3):
            usage = subprocess.check_output(
                ["nvidia-smi", "--query-gpu=utilization.gpu", "--format=csv,noheader,nounits"],
                text=True,
            ).strip()
            if int(usage) > 10:
                raise RuntimeError("GPU busy; no shared-capacity override")
            time.sleep(1)
        memory = dict(line.split(":", 1) for line in Path("/proc/meminfo").read_text().splitlines())
        available = int(memory["MemAvailable"].split()[0]) * 1024
        if not resident and available < installed[args.model]["size"] * 1.25 + 12 * 1024**3:
            raise RuntimeError("Insufficient memory to load the installed model")
        admission = {
            "time": time.time(),
            "host_lock": str(lockpath),
            "model": installed[args.model],
            "initial_resident": resident,
            "memory_available": available,
            "gpu_percent": int(usage),
            "minutes": args.minutes,
            "policy": "One installed local model on idle host; no switch, download or cloud fallback",
        }
        (root / "admission.json").write_text(json.dumps(admission, indent=2) + "\n")
        if not resident:
            print("Loading installed model into idle GPU", flush=True)
            api("generate", {"model": args.model, "stream": False, "keep_alive": "30m"})
        print("Starting sealed 44 proof queue", flush=True)
        deadline = time.monotonic() + args.minutes * 60
        while time.monotonic() < deadline:
            remaining = (deadline - time.monotonic()) / 60
            cp = subprocess.run(
                [
                    sys.executable,
                    str(root / "control/loop.py"),
                    "run",
                    "--model",
                    args.model,
                    "--max-minutes",
                    str(remaining),
                ],
                env={**os.environ, "FORTYFOUR_WORKSPACE": str(root)},
                pass_fds=(lock.fileno(),),
                timeout=remaining * 60 + 750,
            )
            if cp.returncode:
                raise SystemExit(cp.returncode)
            queue = json.loads((root / "queue-state.json").read_text())
            terminal = {"automated_pass", "paused", "human-required", "time-budget"}
            if all(row["status"] in terminal for row in queue.values()):
                print(json.dumps({"terminal_states": {k: v["status"] for k, v in queue.items()}}))
                raise SystemExit(
                    0 if all(row["status"] == "automated_pass" for row in queue.values()) else 3
                )
            # A GPU utilization sample can still include this worker's just-finished call.
            # Wait under the same host lock and preserve every task's persisted attempt count.
            # A different resident model or persistent load still ends the supervised run.
            for _ in range(30):
                if time.monotonic() >= deadline:
                    raise SystemExit(3)
                time.sleep(2)
                resident_now = api("ps")["models"]
                if len(resident_now) != 1 or resident_now[0]["name"] != args.model:
                    raise RuntimeError("Resident model changed; no automatic switch")
                usage_now = int(
                    subprocess.check_output(
                        [
                            "nvidia-smi",
                            "--query-gpu=utilization.gpu",
                            "--format=csv,noheader,nounits",
                        ],
                        text=True,
                    ).strip()
                )
                if usage_now <= 10:
                    break
            else:
                raise RuntimeError("GPU remained busy for 60 seconds; run stopped")
        raise SystemExit(3)


if __name__ == "__main__":
    main()
