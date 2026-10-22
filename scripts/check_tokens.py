"""Source guard for the ControlsLean escape-hatch policy; not a replacement for kernel audit."""

from __future__ import annotations

import re
import sys
from pathlib import Path

FORBIDDEN = re.compile(r"(?<![\w'])\b(sorry|admit|axiom|native_decide|implemented_by)\b(?![\w'])")


def code_only(source: str) -> str:
    """Blank nested comments and ordinary/raw string literals, preserving line positions.

    Lean character literals are skipped too; a quote character inside one must not hide
    the following code. Identifier primes are not character-literal delimiters.
    This is a conservative lexical guard, not a Lean syntax/elaboration implementation.
    """
    output = list(source)
    i = 0

    def blank(start: int, end: int) -> None:
        for j in range(start, end):
            if source[j] != "\n":
                output[j] = " "

    while i < len(source):
        start = i
        if source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        elif source.startswith("/-", i):
            depth = 1
            i += 2
            while i < len(source) and depth:
                if source.startswith("/-", i):
                    depth += 1
                    i += 2
                elif source.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
        elif raw := re.match(r'r(#+)"', source[i:]):
            delimiter = '"' + raw[1]
            end = source.find(delimiter, i + len(raw[0]))
            i = len(source) if end < 0 else end + len(delimiter)
        elif source[i] == '"':
            i += 1
            while i < len(source):
                if source[i] == "\\":
                    i = min(i + 2, len(source))
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        elif source[i] == "'" and (
            i == 0 or not (source[i - 1].isalnum() or source[i - 1] in "_'")
        ):
            # A single character or backslash escape, followed immediately by its quote.
            char = re.match(r"'(?:[^'\\\n]|\\(?:u[0-9a-fA-F]{4}|x[0-9a-fA-F]{2}|.))'", source[i:])
            if char is None:
                i += 1
                continue
            i += len(char[0])
        else:
            i += 1
            continue
        # Interpolated strings can contain Lean terms. Conservatively scan their
        # entire text rather than masking a proof inside an interpolation.
        if source[start] == '"' and start > 0 and source[start - 1] == "!":
            continue
        blank(start, i)
    return "".join(output)


def violations(source: str) -> list[tuple[int, str]]:
    code = code_only(source)
    return [(code.count("\n", 0, hit.start()) + 1, hit[1]) for hit in FORBIDDEN.finditer(code)]


def main(paths: list[str]) -> int:
    if not paths:
        print("usage: check_tokens.py FILE.lean ...", file=sys.stderr)
        return 2
    failed = False
    for filename in paths:
        path = Path(filename)
        for line, token in violations(path.read_text(encoding="utf-8")):
            print(f"{path}:{line}: forbidden token {token}")
            failed = True
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
