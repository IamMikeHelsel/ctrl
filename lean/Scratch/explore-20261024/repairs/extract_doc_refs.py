#!/usr/bin/env python3
"""Extract backticked tokens from doc comments (/-- -/ and /-! -/) in ControlsLean.

Writes TSV lines `token<TAB>file:line` to the path given as argv[1].
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
IDENT = re.compile(r"^[A-Za-z_\u0370-\u03ff][A-Za-z0-9_'.!?\u2080-\u2089\u0370-\u03ff]*$")

out = []
for path in sorted((ROOT / "ControlsLean").rglob("*.lean")):
    text = path.read_text()
    rel = path.relative_to(ROOT)
    for m in re.finditer(r"/-[-!](.*?)-/", text, re.S):
        body = m.group(1)
        body_start = m.start(1)
        body = re.sub(r"```.*?```", lambda b: " " * len(b.group(0)), body, flags=re.S)
        for t in re.finditer(r"`([^`\n]+)`", body):
            tok = t.group(1).strip()
            line = text.count("\n", 0, body_start + t.start()) + 1
            if tok.endswith(".lean") or IDENT.match(tok):
                out.append(f"{tok}\t{rel}:{line}")

pathlib.Path(sys.argv[1]).write_text("\n".join(out) + "\n")
print(f"{len(out)} tokens")
