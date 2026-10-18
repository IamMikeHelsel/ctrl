# Disclosure: Erdős 261 (part i)

- **AI use.** Antigravity / Claude formalization agent wrote `erdos/ErdosLab/Erdos261.lean` and the
  accompanying notes (`plan.md`, `log.md`, `disclosure.md`).
- **Mathematics.** Uses the classical telescoping construction of P. Borwein and T. A. Loring,
  *Some questions of Erdős and Graham on numbers of the form $\sum g_n / 2^{g_n}$*, Math. Comp. 54
  (1990), 377–394 (`n = 2^(m+1) - m - 2`).
- **Statement.** Copied verbatim from Formal Conjectures (`google-deepmind/formal-conjectures` @
  `d9ce556`, `Erdos261.erdos_261.parts.i`, Apache-2.0).
- **Trust base.** Standard Lean 4 axioms only (`propext`, `Classical.choice`, `Quot.sound`). Zero
  `sorry`, zero `native_decide`.
