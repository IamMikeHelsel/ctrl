# Erdős Problem 261 (part i): Infinitely many $n$ with $n / 2^n = \sum a_k / 2^{a_k}$

Source: <https://www.erdosproblems.com/261> · FC: `Erdos261.erdos_261.parts.i`
(`FormalConjectures/ErdosProblems/261.lean` @ `d9ce556`) · Borwein & Loring [BoLo90].

## Why
- Tagged `category research solved` in Formal Conjectures (`Erdos261.erdos_261.parts.i`), with the
  accompanying variants `borwein_loring` and `borwein_loring_property` also in `261.lean`.
- Uncontested in the Justin Sun Prize repository (`jsp_id = none` in `data/erdos/open.csv`).
- Admits a completely self-contained, elementary telescoping-sum proof over `ℚ` using the
  Borwein–Loring sequence $n_m = 2^{m+1} - m - 2$.

## Statement review
FC statement (copied verbatim into `erdos/Challenge/Erdos261.lean`):
`{n : ℕ | 0 < n ∧ Erdos261Prop n}.Infinite`
where:
`def Erdos261Prop (n : ℕ) : Prop := ∃ᵉ (t ≥ 2) (a : Fin t → ℕ), a.Injective ∧ (1 ≤ a) ∧ n / (2 ^ n : ℚ) = ∑ k, (a k) / (2 ^ (a k) : ℚ)`

- Matches Erdős's question [Er88c]: are there infinitely many positive integers $n$ expressible as
  $n / 2^n = \sum_{k=1}^t a_k / 2^{a_k}$ for $t \ge 2$ distinct positive integers $a_k$?
- Non-vacuous: `t ≥ 2` and `a.Injective` rule out the trivial 1-term representation $a_1 = n$.
- Approved by `mike`.

## Blueprint (lemma DAG)
- `sum_range_shifted_div_two_pow` (*elementary*): by induction on $m$,
  $$\sum_{i=0}^{m-1} \frac{n + 1 + i}{2^{n + 1 + i}} = \frac{n + 2}{2^n} - \frac{n + m + 2}{2^{n + m}}.$$
- `sum_Ioc_div_two_pow` (*elementary*): same telescoping identity over `Finset.Ioc n (n + m)`.
- `borwein_loring` (*elementary*): proves `Erdos261.erdos_261.variants.borwein_loring` for all $m > 0$.
- `borwein_loring_property` (*elementary*): proves `Erdos261.erdos_261.variants.borwein_loring_property`
  for all $m \ge 2$ using $t = m$ and $a_i = n + 1 + i$.
- `blSeq_strictMono` & `blSeq_pos` (*elementary*): $k \mapsto 2^{k+3} - (k + 2) - 2$ is strictly
  increasing and positive.
- `solution` (*elementary*): `Set.infinite_of_injective_forall_mem` applied to `blSeq`.
