# Sparse halves in triangle-free graphs: a bound of 131/5000

This repository contains the paper, the flag-algebra certificate, and the Lean
formalization for the following result.

> **Theorem.** Every finite triangle-free graph on `n ≥ 1` vertices contains
> `⌊n/2⌋` vertices spanning at most `(131/5000)·n² = 0.0262·n²` edges.

The paper is [`sparse_halves_simple.pdf`](sparse_halves_simple.pdf).

Erdős conjectured the bound `n²/50`, and offered a prize for a proof. The best
bound previously known was Razborov's `27n²/1024`.

## Contents

| path | what it is |
| --- | --- |
| [`sparse_halves_simple.pdf`](sparse_halves_simple.pdf) | the paper |
| `sparse_halves_simple.tex` | its LaTeX source |
| `clebsch_tangent_certificate.json` | flag-algebra certificate for the four-cycle bound |
| `verify_clebsch_tangent_certificate.py` | exact rational verifier for that certificate |
| `lean/` | Lean 4 formalization, with its own `README.md` and `verify.sh` |

## What rests on what

The proof quotes one external result. Everything else, including the
flag-algebra bound it uses, is proved here.

- **Quoted.** The **max-cut theorem** of Balogh, Clemen and Lidický, that a
  triangle-free graph on sufficiently many vertices has a bipartition with at
  most `2n²/47` edges inside its two sides (Theorem 2(a) of
  `arXiv:2103.14179v1`). The paper removes its largeness hypothesis by a
  balanced blow-up argument.
- **Proved here, not quoted.** A **lower bound on the four-cycle density**,
  `t(C₄,G) ≥ ρ³ − γρ` with `γ = 3/64 + 1/(5·10¹⁰)` and `ρ` the edge density,
  by a flag-algebra certificate that is checked exactly in this repository.

Apart from those two ingredients the argument is elementary and carried out by
hand in the paper: a rounding lemma, a perturbation supported on the
neighbourhood of a single vertex, and a one-variable optimization.

## Checking the certificate

```sh
python3 verify_clebsch_tangent_certificate.py
```

Requires Python 3 and NetworkX; everything else is standard library. All
arithmetic is exact (`fractions.Fraction`), so no floating-point comparison
enters any sign decision. The script re-derives the coordinate ordering from
the hosts rather than trusting stored data, and cross-checks the host list
against NetworkX's graph atlas. Expected output:

```
verified triangle-free six-vertex hosts: 38
verified rational rank-one squares: 34
minimum slack host: 0
minimum slack: 0
minimum slack decimal: 0.0
epsilon used: 1/50000000000 2e-11
epsilon actually needed by these exact factors: 37066776156390565700818918914980643814154598060079832339619995412234266583535287075150307041372901207/1861706249374902154777225186717734242817175930622749440265668132389240657636512268579835194512385601318298632000 1.991010996973144e-11
```

The last line is the exact `ε` that these factors require, just under the
`2·10⁻¹¹` the certificate uses. The minimum slack is exactly zero because the
inequality is tight at the Clebsch graph, which is why `γ` carries the small
`1/(5·10¹⁰)` term.

## Checking the formalization

```sh
cd lean
./verify.sh
```

This builds the package and prints, for each conclusion, the axioms it depends
on. All five report exactly Lean's three standard axioms:

```
[propext, Classical.choice, Quot.sound]
```

There is no `sorry`, no `admit`, no `native_decide`, and no added axiom.

**What the Lean development proves.** The max-cut theorem above is taken as an
explicit hypothesis of the formalized theorem, so it appears in the theorem's
statement rather than being reproved. The four-cycle bound is *not* assumed: it
is proved inside the development, together with the flag-algebra machinery it
needs. So the Lean endpoint is the `131/5000` bound conditional on the quoted
max-cut theorem, and the conditionality is visible in the types. See
`lean/README.md` for the statement-by-statement correspondence with the paper.

## Notes

The constant is close to, but not exactly, the best this argument gives. The
high-density and low-density branches balance at an edge density near `0.3184`,
where both give about `0.026176`; the paper splits at the nearby short rational
`7/22` and states a short decimal, which together cost about `2·10⁻⁵`.

OpenAI's GPT-5.6 Sol and Anthropic's Claude Fable 5 assisted in the
research, writing and formalization of this work.
