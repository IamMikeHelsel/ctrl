#!/usr/bin/env python3
"""Classify all emitted K_3,>=6 grids up to square scaling."""
from collections import defaultdict
from fractions import Fraction
from math import gcd, isqrt
from pathlib import Path


def parse(line: str) -> tuple[list[int], list[int]]:
    left, right = line.split(" d:")
    ns = [int(x) for x in left.split(" N:")[1].split()]
    ds = [int(x) for x in right.split()]
    return ns, ds


def divisors(n: int) -> list[int]:
    small, large = [], []
    for d in range(1, isqrt(n) + 1):
        if n % d == 0:
            small.append(d)
            if d * d != n:
                large.append(n // d)
    return small + large[::-1]


def primitive(ns: list[int], ds: list[int]) -> tuple[int, tuple[int, ...], tuple[int, ...]]:
    gd = gcd(*ds)
    scale = max(t for t in divisors(gd) if all(n % (t * t) == 0 for n in ns))
    return scale, tuple(n // (scale * scale) for n in ns), tuple(d // scale for d in ds)


def main() -> None:
    lines = [
        line for line in Path("all_k36.txt").read_text().splitlines()
        if line.startswith("K_3,")
    ]
    classes: dict[tuple[tuple[int, ...], tuple[int, ...]], list[int]] = defaultdict(list)
    for line in lines:
        ns, ds = parse(line)
        t, pns, pds = primitive(ns, ds)
        classes[(pns, pds)].append(t)

    with Path("structures.txt").open("w") as out:
        print(f"literal_grids={len(lines)} primitive_scaling_classes={len(classes)}", file=out)
        for i, ((ns, ds), scales) in enumerate(classes.items(), 1):
            print(f"\nclass {i}: scales={sorted(scales)}", file=out)
            print("N:", *ns, file=out)
            print("d:", *ds, file=out)
            print("N/N0:", *(str(Fraction(n, ns[0])) for n in ns), file=out)
            print("d/d0:", *(str(Fraction(d, ds[0])) for d in ds), file=out)
            print(f"gcd(N)={gcd(*ns)} gcd(d)={gcd(*ds)}", file=out)


if __name__ == "__main__":
    main()
