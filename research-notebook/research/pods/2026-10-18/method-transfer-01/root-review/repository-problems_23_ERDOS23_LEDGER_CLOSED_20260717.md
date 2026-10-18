# Erdos Problem 23: Ledger Closure

Date closed: 2026-07-17
Closed by: user decision of 2026-07-17 ("convert the results into publishable
work and close the #23 ledger"), following the program-wide halt of the same
day (asymptotic-reformulation verdict; see the memory record and PROGRESS.md).

This note is the formal end of the Erdos #23 working ledger. It supersedes
nothing in ERDOS23_FINAL_HANDOFF_20260712.md, which remains the technical
restart record; it adds the publication outcome and the final artifact map.

## 1. Final status of the mathematics

    The Erdos n^2/25 conjecture (bip(G) <= N^2/25 for triangle-free G) is OPEN.

Proved and published: a(5n) = n^2 for 1 <= n <= 40 (all multiples of five up
to N = 200), arXiv:2606.28041 [math.CO].

No unconditional all-order theorem was obtained. The precise remaining wall is
Section 3 of ERDOS23_FINAL_HANDOFF_20260712.md (graph-derived full-bank
provider, or the closed-shore/restricted-Farkas equivalent).

## 2. Publications produced by the program

1. PUBLISHED: Alper Ferudun, "The Erdos n^2/25 max-cut conjecture for small
   multiples of five, via a per-root-MaxCut envelope and blow-up integrality",
   arXiv:2606.28041 [math.CO], 2026.

2. SUBMITTED (on hold in moderation at closure): "Shortest-geodesic supports
   in triangle-free maximum cuts: an infinite Hall obstruction and the first
   minimal footprints", arXiv submit/7816436, submitted 2026-07-12, math.CO,
   CC BY 4.0. Source + ancillary: problems/23/writeup/arxiv/
   shortest_support_obstructions/ (anc manifest replayed 7/7 OK on
   2026-07-17; both family verifiers PASS; footprint recheck matches the
   printed classification).
   Release artifacts (SHA-256):
     output/pdf/shortest_geodesic_support_obstructions.pdf
       67DD92FEF8376B81091327CDA1CDA5690603BBAC7C4E0A8B6AEEB4BF0E7BBCFB
     output/pdf/shortest_geodesic_support_obstructions_arxiv.zip
       6831828B86D5151DCEC5C29869536E65D2B4B1D5EF0ABA96498E4BF4DBF2943C

3. SUBMITTED (on hold in moderation at closure): "Balanced deficiency rotors
   in shortest-support Hall systems of triangle-free maximum cuts",
   arXiv submit/7837759, submitted 2026-07-17, math.CO, CC BY 4.0,
   MSC 05C35. 31 pages; compiled SUCCEEDED on arXiv pdflatex
   (TeX Live 2025), zero errors, no unresolved references.
   Contents: support-circuit identity (|F*| = m-1, deletion-SDR bijections,
   incidence connectivity, transversal-matroid circuits); star lemma at
   cut-tight vertices (arithmetic core kernel-checked in Lean 4); the
   eight-vertex neutral square rotor; the t=3 closure (two independent
   proofs, Lean cores); the t=4 sixteen-atom closure (dual-verified census
   of 153,978 graphs; 576 windows all at 15 vertices vs the covered bound
   of 14); partial t=5 results (order window 15..21, orders 15/16 excluded,
   circuits #298/#264 excluded by dead-owner + ambient-extension
   certificates, orders 17/19-21 open). Every computer-assisted claim
   ships its verifier and artifacts in anc/ (75-file SHA-256 manifest;
   the twelve t=5 split certificates regenerate bit-exactly).
   Source of record: problems/23/writeup/arxiv/rotor_window_closures/
   (main.tex + sections/ + anc/ + CLAIMS_LEDGER.md + six adversarial
   referee reports).
   Release artifacts (SHA-256):
     output/pdf/rotor_window_closures_arxiv.zip (submitted package)
       501C3D8E9CAE6EFEA4332AEBFB873BE0CC5CC8FEC38CDCBFB675BE51D64EDFB9
     output/pdf/rotor_window_closures_arxiv_compiled.pdf (arXiv AutoTeX
     output retrieved at submission)
       4C86BCF1B852F7BA31BBB0AE9FC56FEE8921DC936ACDC4D9E9EE23917D008483

## 3. Verification state at closure

- Paper 2 was drafted from the R38-R53 wall archives by section agents,
  adversarially refereed per claim (six reports, all issues fixed at
  assembly), and every by-hand proof was independently re-verified line by
  line at the final gate. The self-contained 20260712 replay-audit bundle
  reran PASS (runs=9, report SHA 9682E88E...) on 2026-07-17.
- The Lean modules cited in Paper 2 carry dual attestation, including a fresh
  2026-07-17 rebuild + axiom probe of LiveMiddleSwapCrossOuter
  (axioms exactly [propext, Quot.sound]).
- Claims deliberately EXCLUDED from publication (unverified or superseded)
  are listed in rotor_window_closures/CLAIMS_LEDGER.md; nothing unverified
  was published.

## 4. Post-closure obligations (user)

1. Watch arXiv moderation for submit/7816436 and submit/7837759
   (notifications to alper@mercurycodelab.com). Both were on hold at closure;
   this is a moderation queue state, not an error.
2. When the companion (submit/7816436) is announced, add its arXiv
   identifier to the Ferudun26supports bibitem of Paper 2 (a v2 replacement)
   and cross-link the two abstracts.
3. The open questions stated in the papers (graft question for the rotor;
   t=5 scope-vacuity; windows (5,2)/(5,3)) are honest open problems for
   any future reader; no obligation remains on this repository.

## 5. Standing rule

Per the 2026-07-17 halt: no Erdos proof loop, workflow, wakeup chain, or
enumeration restarts for #23 (or #424/#864) unless the user explicitly asks.
The ledgers, archives, and Lean trees remain read-only records.
