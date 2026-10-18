# Disclosure: Erdős 931 (`additional_condition_nonempty`)

- **AI use.** Antigravity / Claude formalization agent searched for symmetric $k_1 = k_2 = 3$
  positive-integer counterexamples in Python and formalized `erdos/ErdosLab/Erdos931.lean`.
- **Mathematics.** Strengthens AlphaProof's degenerate $(k_1, k_2, n_1, n_2) = (10, 3, 0, 13)$
  counterexample to positive-integer symmetric $k_1 = k_2 = 3$ witnesses $(n_1, n_2) = (2, 7)$
  ($3 \cdot 4 \cdot 5 = 60$ and $8 \cdot 9 \cdot 10 = 720$, prime factors $\{2, 3, 5\}$) and
  $(n_1, n_2) = (3, 7)$ ($4 \cdot 5 \cdot 6 = 120$ and $8 \cdot 9 \cdot 10 = 720$).
- **Statement.** Copied verbatim from Formal Conjectures (`google-deepmind/formal-conjectures` @
  `d9ce556`, `Erdos931.erdos_931.variants.additional_condition_nonempty`, Apache-2.0).
- **Trust base.** Kernel `decide +kernel` only; standard Lean 4 axioms (`propext`,
  `Classical.choice`, `Quot.sound`).
