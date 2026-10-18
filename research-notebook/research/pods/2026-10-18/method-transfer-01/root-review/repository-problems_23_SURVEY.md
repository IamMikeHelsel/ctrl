# Erdos problem #23 survey

## Core references

- Problem page: https://www.erdosproblems.com/23
- OEIS A389646: https://oeis.org/A389646
- Balogh, Clemen, Lidicky, "Max Cuts in Triangle-free Graphs",
  arXiv:2103.14179.
- McKay data page:
  https://users.cecs.anu.edu.au/~bdm/data/graphs.html

## Frontier

OEIS A389646, checked again on 2026-06-11, currently lists exact values
through `n=23`:

`0, 0, 0, 0, 1, 1, 1, 2, 2, 4, 4, 5, 6, 7, 9, 9, 10, 12, 13, 16, 16, 17, 20`

with `a(23)=20` credited to Brendan McKay. McKay's `minbip` data page states
that `minbip N_Ax.g6` contains all triangle-free graphs on `N` vertices
achieving `a(N)=A`; without `x` is only the maximal-triangle-free subset.

The Erdős Problems page for #23 is still marked open (checked 2026-06-11),
and its comment area reports no partial or complete solution claims.

Balogh-Clemen-Lidicky prove the Erdos `n^2/25` bound for triangle-free graphs
in low- and high-density regimes, including high-density threshold `0.3197`.
They also give the global upper bound `a(n) <= n^2/23.5`.

## New result from this project

`a(25)=25` is proved in:

`E:\Projects\ErdosProblems\docs_newmath\erdos23_a25_proof.md`

Formal Conjectures PR:

https://github.com/google-deepmind/formal-conjectures/pull/4216

This appears novel relative to OEIS/McKay public exact values, which stop at
`n=23`.

## Active frontier target

Try to prove `a(30)=36`.

Current finite route:

No triangle-free graph on 30 vertices has `beta >= 37`. By BCL high density,
it is enough to consider `e <= 139`; by BCL low density, the range `e <= 108`
is already impossible, so the hard medium-density window is

`109 <= e <= 139`.

The older sufficient certificate "no 29-vertex graph has `beta >= 33` and
`e <= 139`" is too blunt. The current rooted target uses a minimum-degree
vertex of degree `r=4..9` and the exact rooted cut condition on `G-v`.
