# Disclosure: Erdős 834 (part ii)

- **AI use.** Claude Code (Anthropic, model Claude Opus) did this work. It chose the problem,
  copied the Formal Conjectures statement, wrote the Lean proof `lean/ErdosLab/Erdos834.lean`,
  re-checked the witness in Python, and wrote this folder's notes (plan.md, log.md). None of it is
  hand-written. A human still has to review and approve the statement.
- **Mathematics.** The hypergraph comes from R. Li, *On an Erdős–Lovász problem: 3-critical
  3-graphs of minimum degree 7*, arXiv:2512.24850 (2025). The formal proof just checks Li's
  example; it adds no new mathematics.
- **Statement.** It is copied verbatim from Formal Conjectures (google-deepmind/formal-conjectures
  @ d9ce556, `Erdos834.erdos_834.parts.ii`, Apache-2.0).
- **Trust base.** Kernel `decide` only (no `native_decide`, no `Lean.ofReduceBool`). Axioms:
  propext, Classical.choice, Quot.sound.
