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

## Crossover follow-up on 2026-10-18

- **AI use.** OpenAI Codex developed the MaxCut/Ising interpretation, exact Python search and
  independent certificate replay, the four-leaf structural Lean reproof, generic coloring lemmas,
  and follow-up exposition. A dedicated Codex program-manager subagent reviewed scope/evidence and
  wrote `docs/crossover-program-report-2026-10-18.md`. This follow-up is AI-written.
- **Change.** The hypergraph and challenge statement are unchanged. The non-two-colorability
  proof now uses color complementation, three binary branch nodes, and forced not-all-equal
  constraints. Vertex criticality is derived from edge criticality and positive degree, replacing
  the separate nine-coloring table. The original 22 edge-deletion witnesses remain.
- **Mathematics and priority.** This is a structural reproof of Li's existing example and reusable
  elementary lemmas, not a newly solved Erdős problem. No novelty claim or external submission.
- **Trust base.** The updated proof uses ordinary Lean proofs (`omega` and kernel `decide` among
  its tactics), with only propext, Classical.choice, Quot.sound. Python/LP/SDP results are not
  trusted axioms. The exact clique LP certificate is Python evidence; the numerical SDP attempt
  is only a failed-search diagnostic. Statement approval remains a human action.
