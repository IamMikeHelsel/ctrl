"""Compile work/pod/885/smooth/search.cpp and run it in the job's outputs/ dir.

usage: spark_smooth.py X Y KMIN KMAX [search args...]
Writes hits.txt (search output) and run.log (stderr progress) in cwd.
"""

import shutil
import subprocess
import sys
from pathlib import Path

src = Path(__file__).resolve().parents[1] / "pod" / "885" / "smooth" / "search.cpp"
cxx = shutil.which("clang++") or shutil.which("g++")
if cxx is None:
    sys.exit("no C++ compiler on PATH")
subprocess.run([cxx, "-O3", "-std=c++17", "-pthread", str(src), "-o", "search"], check=True)
x, y, kmin, kmax, *rest = sys.argv[1:]
with open("run.log", "w") as log:
    rc = subprocess.run(["./search", x, y, kmin, kmax, "hits.txt", *rest], stderr=log).returncode
print(Path("run.log").read_text()[-3000:])
print(Path("hits.txt").read_text())
sys.exit(rc)
