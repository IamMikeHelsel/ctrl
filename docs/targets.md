# Targets

## Data
`data/erdos/open.csv` (642 open problems) and `data/erdos/formalize.csv` (263 solved problems with
no Lean solution yet) are snapshots from 2026-10-17. They were built by `tools/erdos-assess/` from the
teorth/erdosproblems database (commit b850d1a), the erdosproblems.com pages, and the Justin Sun Prize
catalog. Ratings are quick model judgements, so re-check before investing. The columns are explained
in the Drive workbook's README tab. erdosproblems.com text is deliberately not stored here.

Start with:
- **formalize.csv, effort ≤ 2**, for example 834, 895, 1213, 1216, 915, 473. A Lean solution of a
  solved problem is publishable on Palomar, and the Justin Sun Prize has paid formalizer-only awards.
- **open.csv, possibly_resolved = yes** (48 rows). A claimed proof exists, so verify it and formalize it.
- **open.csv, prize with route = finite computation / construction.** These are 647, 99, 132 and 708.

## Payout and submission rules (summary)
- **Erdős prize** (Combinatorics Foundation, Steve Butler): requires a journal publication plus proof
  that Erdős offered the amount.
- **erdosproblems.com listing**: comments and proof claims have been frozen since 2026-10-06. Send a
  Lean proof registered on Palomar (challenge + solution + `formalization.yaml`, checked by Comparator
  and the kernel) plus a self-written exposition with honest AI disclosure, by email.
- **Justin Sun Prize** (github.com/TheJustinSunPrize/awards): the legacy process takes complete
  solutions only. Lean submissions must come with the math solution and its evidence. The process is
  a PR, then a claim issue, a 14-day public review, KYC, and payment in USDT/USDC. Amounts are not
  published. The MathDB pilot pays 50/30/20 for solution, Lean and exposition, for work first made
  public after 2026-01-01.

Full details are in the Drive doc "Erdős Problems — Targets & Submission Guide".
