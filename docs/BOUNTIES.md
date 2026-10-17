# Bounty and prize sources for Lean solves

Verified from primary sources on 2026-10-17 unless marked otherwise. Amounts and rules change
often, so re-check the organiser's own page before investing effort.

## Lanes that pay money

### 1. Justin Sun Prize (JSP), the best fit for formalization work
* Rules: <https://www.hejustinsun.com/prize/rules>
* Records and process: <https://github.com/TheJustinSunPrize/awards> (`docs/award-process.md`,
  `docs/verification.md`, `problems/`)
* Pays the **Lean formalizer separately from the mathematical solver** (legacy process:
  70% solver / 30% formalizer). A formalizer can claim a problem someone else already solved,
  provided a complete published solution exists and passes review. This is the lane where
  "formalize a known proof" earns money.
* Only Lean counts. The proof must be complete, with no `sorry` and standard axioms only.
  Submissions that state literature results as axioms are closed.
* **Priority goes to the earliest public commit of a complete proof**, not the PR date. The proof
  must live in our own *public* repo, pinned by a 40-character SHA.
* Paid in USDT/USDC with mandatory KYC. An AI cannot be the payee; a person or company can.
* Reality check: about 1,870 open issues and PRs, a long review backlog, and few confirmed
  awards so far. Treat payouts as slow and uncertain.
* The repo ships a `skills/lean-verify` self-check. Run it before submitting.

### 2. conjectures.io
* <https://conjectures.io>, <https://conjectures.io/how-it-works>
* Exact Lean statements of **open** problems, taken from DeepMind's Formal Conjectures. Prove
  or refute; the first accepted proof wins. Per-problem bounties were about $1.8k–4.6k in Oct 2026.
* Costs 0.25 τ per verification attempt. Paid in Bittensor alpha (crypto). Chat logs are required.
* These are genuinely open research problems. Only attempt one with a real mathematical idea.

### 3. Grants (fund the program rather than pay per solve)
* Renaissance Philanthropy / XTX **AI for Math Fund**: <https://www.renaissancephilanthropy.org/ai-for-math-fund>.
  Grants of $100k–1M, plus seed grants up to $100k for tools, datasets, and prototypes. A
  "verified controls and vision library" fits the tools/datasets category.

## Lanes that build credibility (no money)

* **Palomar registry** (Lean FRO + ICARM, launched 2026-08-18): <https://palomar-registry.org/about>.
  A citable, machine-checked record. AI work is allowed with disclosure in `formalization.yaml`.
  There is a research-interest floor, so textbook results won't pass. It requires the Lean
  `module` system and a `Challenge.lean`/`Solution.lean` split.
* **Formal Conjectures** (DeepMind): <https://github.com/google-deepmind/formal-conjectures>.
  Contributions are new statements, fixes for misformalizations, and solved-status updates.
  Requires a Google CLA and follows Mathlib's AI policy.
* **Mathlib**: <https://leanprover-community.github.io/contribute/index.html>. Disclose LLM use
  and add the `LLM-generated` label. Discuss on Zulip first.
* **SAIR competitions** (XTX-funded, recognition only, full legal name required):
  Lean Kernel Challenge (deadline 2026-11-20,
  <https://github.com/SAIRcompetition/lean-kernel-challenge>) and Andrews–Curtis
  Challenge (deadline 2026-11-30).

## Closed or not paying (don't chase)

* AIMO Progress Prizes: XTX closed the series on 2026-09-16.
* FrontierMath Erdős (Epoch AI): a benchmark, not a bounty.
* Self-declared GitHub "bounties" with no funder or escrow.
* asiprize.com "LeanCoin": lists dollar figures, but the stated payout is one LeanCoin token. Unverified.

## Secondary sources

* <https://github.com/munimv2/formal-math-bounties> is a maintained survey (itself AI-written).
  Use it to discover programs, then verify against primary pages.
* Terence Tao's blog and the Lean Zulip `#Palomar` and `#Erdős problems` channels.

## Our pipeline for bounty targets

The formal-conjectures snapshot (2026-10-17) has 1,137 Erdős problems: **680 tagged
`research solved` with the proof still `sorry`**, and 457 tagged open. Solved-but-unformalized
problems are the realistic money lane: JSP formalizer share, plus a Palomar entry and an
upstream Formal Conjectures update.

1. `scripts/bounty_triage.sh` lists solved Erdős statements, shortest first. Short statements
   with elementary solutions are the best first targets.
2. For a candidate, find the published solution (erdosproblems.com page, then the paper)
   and confirm the JSP problem bank lists it (`problems/` in the JSP repo).
3. Check JSP PRs and issues for existing formalizations of that problem ID. Skip any that
   are already recorded.
4. Formalize the problem in `ControlsLean/Bounty/ErdosNNN.lean` against the *exact* upstream
   statement (copy it verbatim and pin the formal-conjectures commit). Full `check.sh`.
5. Push to a **public** repo immediately (`ctrl` is private for now, per Mike; decide on a public home before submitting anything) to fix priority. Then run JSP `lean-verify`, open the
   PR, and add a Palomar submission if the result clears the research-interest floor.
