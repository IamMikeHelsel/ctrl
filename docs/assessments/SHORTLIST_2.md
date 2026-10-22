# JSP shortlist, round 2 — Solved / Lean proof: No (screened 2026-10-17)

## Bottom line

**No entry among the 294 meets both criteria (not formalized publicly, and formalizable within days).**
The pool is saturated. Every entry falls into one of three groups:

- It already has a complete public Lean proof. For Erdős problems this is mostly plby/lean-proofs;
  others come from OpenAI, formal-conjectures (FC) `formal_proof` links, or claimants' repos.
- It has a public repo that claims a complete proof (axiom-clean according to its README) and an open awards PR.
- It is a famous or deep theorem, or one whose published proof appears to have a gap.

The table below is therefore the **least-saturated** set, ranked by remaining opportunity. It is not a list
of recommended targets.

## How saturation was established

1. **plby/lean-proofs** (sparse clone, HEAD 2026-09-15): `src/latest/ErdosProblems/` holds 603 problem files.
   Its own `ErdosProblems/PROGRESS.md` (snapshot 2026-08-27) reports "601 formalized · 4 solved, not
   formalized here (216, 504, 599, 610)". E599 (Erdős–Menger) has since been added. plby is effectively
   `sorry`-free; the 30 textual `sorry` hits are all in comments. plby also covers the non-obvious ones:
   Duffin–Schaeffer (E999), circle squaring (E1124), the random-walk problems (E1164–1166), the most
   probable permutation order (E1161), and the Erdős–Simonovits compactness disproof (E180, which is
   OpenAI's own Lean and also covers E575).
2. **teorth/erdosproblems `data/problems.yaml`** (main, 2026-10-17): among solved problems, only
   E216, E504, E575, E625 and E1219 are neither "Lean" nor in plby. E1219 has an FC `formal_proof` link.
   E193 and E610 carry external Lean links.
3. **The OpenAI Sept/Oct 2026 results** (Hindman sums/products, hypercube Ramsey, higher-dimensional
   distinct distances, Artin) are 70–172-page papers. Public repos by `cadamcat` (84 to 1,689 Lean
   files, created 2026-10-07..10) claim complete formalizations of each.
4. **Awards PR/issue counts for all 294 entries** (`gh pr|issue list --state all --search JSP-…`).
   Distribution of PR counts: 0 PRs: 1 entry, 1 PR: 2, 3 PRs: 2, 4–9 PRs: 249, 10+ PRs: 40.
   269 of the 294 entries have a bulk "register Lean formalization (plby/lean-proofs)" PR.

## Ranked table (least-saturated; none is a recommended target)

| Rank | JSP id | Title | Area | Solved (date / source) | Awards PRs / issues | Existing formalization | Why tractable | Main risk |
|---|---|---|---|---|---|---|---|---|
| 1 | JSP-000404 | Blumenthal's problem (E504) | Discrete geometry | Sendov 1992/93, final Theorem 4.1 (1995 exposition) | 9 / 0 | **Partial only.** PR #100: exact α_N for N=5–10 and all N=2^n. PR #300: "unconditionally provable part". `jerrylijize1224-star/jsp404-lean-partial` (2026-10-14): 139.09° ≤ α₁₇ ≤ 140°. `Jackie1021/jsp000404-lean`, `DF-dan/jsp-000404-sendov-audit`. `Yi-111-a` is a scaffold whose headline theorem is still `sorry`. Not in plby or FC. | The only in-scope entry with no complete or claimed-complete proof. Dyadic and small-N infrastructure (MIT) already exists | Several groups report that **the general lower-bound step in Sendov's proof is missing** (Lemma 4.10 weight exponent; α₁₇ unresolved). Likely research-level, not days. Crowded field |
| 2 | JSP-000506 | χ − ζ gap in G(n,1/2) (E625) | Random graphs | Heckel 2024 / Steiner 2024; Petkov manuscript | 11 / 2 | **Claimed complete:** PR #363 (`ketianzhang1-lang/jsp-000301-lean@2aca2f1`, `JSP000506.jsp_000506`, top-level file has no `sorry`, dependencies not audited). PR #4552 (CreizyLabs) proves a deterministic toy statement, not the problem. plby lists E625 as "Open". | An opportunity only if the #363 claim fails an audit | Random-graph probability is heavy in Lean; there is an earlier public claimant |
| 3 | JSP-001059 | Hilbert 16th: uniform limit-cycle bound | Dynamical systems | OpenAI preprint 2026-09-24 (review pending) | 0 / 0 | OpenAI Lean covers only the quintic Liénard case (`OAI.QuinticLienard.main`) | Zero competing PRs | Deep, unreviewed manuscript; weeks to months. Out of scope |
| 4 | JSP-001068 | Ionization conjectures (Coulomb) | Mathematical physics | OpenAI preprint 2026-09 | 1 / 0 | OpenAI partial Lean; PR #5063 claims Lean | Few PRs | Deep spectral theory. Out of scope |
| 5 | JSP-001071 | Grothendieck homotopy hypothesis | Higher categories | OpenAI preprint 2026-09-24 | 1 / 0 | OpenAI partial Lean (`elementary_expansion`); PR #5068 claims Lean | Few PRs | Deep. Out of scope |

## Notable rejects (saturated)

| JSP id | Reason |
|---|---|
| JSP-000198 (E216) | `peilinliu66-dev/jsp-000198-lean` (2026-10-05) claims the complete classification: g(3..5) exact, g(6) exists via Nicolás, Horton for k≥7, axioms `propext`/`Classical.choice`/`Quot.sound` only. 8 PRs, 2 issues |
| JSP-000465 (E575) | OpenAI `ten-proofs/CompactnessAndDegeneracy.lean`, vendored in plby `Erdos180` (`not_erdos_180`, standard axioms). 9 PRs, 4 issues |
| JSP-000168 / -000175 / -000900 / -000027 | OpenAI Sept/Oct 2026 results (70–172 pp.). `cadamcat/*-lean4` repos claim complete Lean (PRs #4966, #4967, #4994, #4970); #5075 is a second claimant for 168 |
| JSP-000183 (E193) | `ekalvi/erdos-193` Lean (2026-09-02). 11 PRs |
| JSP-000832, -000934, -000085 | Duffin–Schaeffer (plby E999), circle squaring (plby E1124), discrepancy problem: all in plby |
| JSP-000966, -000969..971 | plby E1161 and E1164–1166 |
| JSP-000007, -000018, -000035, -000036 | Famous or deep (Poincaré, sofa, Catalan, modularity); each has 3–16 PRs with dubious "kernel-verified" claims |
| E1219 entry | FC `1219.lean` carries `formal_proof using lean4` |
| All other Erdős-derived entries | Solved on erdosproblems.com and formalized in plby (601 problems, Comparator-checked), with bulk "register plby" awards PRs |

## Counts

Examined: **294 / 294** at the coverage level (plby progress page, teorth tracker, FC, OpenAI CONTENTS,
and awards PR/issue counts for every entry). About 25 were checked in depth (claimant repos cloned, or
README, axiom and `sorry` checks).
Saturated, meaning a complete or claimed-complete public Lean proof exists: **287**.
Not saturated: **7**. Six of these are out of scope as famous or deep: JSP-000007, -000018, -000036,
-001059, -001068 and -001071. The first three have only dubious claims. One is in scope but blocked by an
apparent gap in the published proof: JSP-000404.
In-scope candidates meeting both criteria: **0**.

## Suggested pivots

1. **Audit existing "complete" claims.** Priority goes to the earliest *complete* commit, so a claim that
   fails an audit (as CreizyLabs' JSP-000506 does) reopens the entry. Start with JSP-000506 PR #363 and the
   `cadamcat` repos.
2. Watch Open→Solved transitions after 2026-10-17, and the MathDB pilot entries (`problems/mathdb-pilot.json`).
3. JSP-000404 is only viable as a research project: close the Sendov lower-bound gap for general N.
