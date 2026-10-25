# JSP "complete Lean" claim audit — 2026-10-17

Scope: the 294 JSP catalog entries marked `Solved, Lean: No` (`jsp_solved_no_lean_2026-10-17.json`),
of which the earlier screen found 287 with a complete or claimed-complete public Lean proof.
This audit checks how solid those claims are. Information gathering only; no proofs written, no builds run.

## Bottom line

- **No entry is cleanly reopened.** Every weak primary claim we found has either a second, stronger
  public proof, or a gap that is practically infeasible to close (JSP-000198).
- **Priority moves away from the obvious claimant** on JSP-000078, 000320, 000506, 000512 (conditional)
  and 000733. That matters for who gets paid, but it doesn't open a slot for us.
- **Mechanical checks are clean.** Across plby, cadamcat, PR #363 / Petkov and the competitor repos:
  no code-level `sorry`/`admit`; no custom axiom used by any target theorem; `native_decide` appears only
  in plby `Erdos402.lean`, in lemmas the final theorem doesn't use.
- **The bulk catalog-registration PRs** (dcdreamy-code, about 1000 open PRs, 260 of them on our 294 entries)
  are third-party "register plby" PRs. The rules forbid registering someone else's proof, and at least
  15 of them point at the wrong Erdős file. These are attribution and registration problems only:
  the correct plby file exists in every case.

## Method

1. **Sources cloned shallowly into `/tmp/audit`:**
   - plby/lean-proofs at `8822f7dd` (2026-09-15): sparse `src/latest/ErdosProblems`, plus all 628
     `ComparatorChallenges/ErdosProblems/*.lean` fetched raw
   - all 12 cadamcat repos
   - PR #363 branch `ketianzhang1-lang/jsp-000506-complete-kz`
   - SamPetkov/Erdos, CollinYuanjieRen/awards (`proofs/jsp-000320-cyr`)
   - devin-lai/jsp-000512-lean, peilinliu66-dev/jsp-000198-lean, ekalvi/erdos-193
   - kunjunsong-code/jsp-batch2-lean, CHENLexiao8848/jsp-000637-lean
   - TheJustinSunPrize/awards
2. **Grep checks:** `sorry`, `admit`, `^axiom`, `native_decide`, `decide +kernel`, then a manual check
   that each hit is real code rather than a comment.
3. **Statement comparison:** the catalog statement (`/tmp/jsp_catalog_all.md`) against the Comparator
   challenge theorem or the main theorem, done by hand, for about 38 plby entries, all cadamcat repos, PR #363,
   and the competitor repos above. Where it exists, also compared with the formal-conjectures (FC) statement.
4. **Rules:** TheJustinSunPrize/awards rules plus the `lean-verify` skill text:
   - Special cases, weaker results and conditional arguments do not qualify.
   - `native_decide` is "extended trust", not automatically disqualifying.
   - Priority goes to the earliest commit in the original repo. No mirrors, and no registering on someone else's behalf.
   - MathDB pilot: Lean and solution must both have become public after 2026-01-01.
5. **Not done:** builds. Every repo is large: plby has about 600 problem files, cadamcat repos have 450–1700
   files, and Petkov has about 480 modules, all on Mathlib. "Doesn't build" is therefore **unverified** throughout.

## Mechanical findings

| Source | sorry/admit | axiom | native_decide | Notes |
|---|---|---|---|---|
| plby `ErdosProblems/` | none in code; all hits are comments (e.g. Erdos369:1162) | `ErdosProblems/Axioms.lean` declares `dusart_mertens_product`, `dusart_pi_lower`, `dusart_pi_upper`, `dusart_chebyshev` | `Erdos402.lean` only (23 uses) | Axioms.lean is imported by E237/E427/E659, but none of those four names is referenced anywhere, so they are inert. The other declarations there are proved theorems. `axiom qc` in `Erdos49/PNT/Tactic/AdditiveCombination.lean` is inside a doc comment. `native_decide` in E402 sits only in the \|A\| ≤ 7000 lemmas, which the eventual-form challenge theorem doesn't use. E1038 uses kernel `decide`, which is fine. |
| cadamcat (12 repos) | only in `Challenge.lean` stubs and audit negative-control fixtures | only in a negative-control fixture | none | Attribution is transparent: builds on openai/math modules. |
| PR #363 (`jsp-000506-complete-kz`) / SamPetkov/Erdos | none | none | none | Petkov's README states the trust boundary as the standard three axioms. |
| CollinYuanjieRen `proofs/jsp-000320-cyr` (157 files) | none | none | none | |
| devin-lai/jsp-000512-lean | none | none | none | |
| peilinliu66-dev/jsp-000198-lean | none | none | none | `remainingCaseIACore` is proved, so the result is unconditional. |

## Per-entry findings

Severity: **HIGH** = the primary claim doesn't qualify as written; **MED** = arguable statement mismatch
or a partial result; **LOW** = cosmetic or acceptable; **OK** = statement matches and checks are clean.

| Entry | Claimant repo/commit | Issue found | Severity | Reopens bounty? |
|---|---|---|---|---|
| JSP-000320 (Erdős 387) | plby `Erdos387` (first 9bd4cd01, 2026-08-16; last cecc3fc4, 2026-08-24) | `not_erdos_387` is **conditional**: hypothesis `h : ∀ B K, 3 ≤ B → ∀ S : BPZSection6Input B K, ∃ … < (RefinedSiftedCandidates S X z).card`. The FC/catalog statement is unconditional. | HIGH | **No (contested).** CollinYuanjieRen/awards@0f6c715e (2026-09-16) proves an unconditional `erdos_387 : False ↔ …` on top of plby and FormalPantheon. Its PR #296 was closed by GordonLtron over identity mismatch (maintainer status unverified). zjukop3's claim #2057 covers only Schinzel's `(n−k, n]` case, which is weak. Watch it, but don't target it. |
| JSP-000512 (Erdős 631) | plby `Erdos631` (first b7d58b8c, 2026-08-17) | `IsPlanar` is a custom recursive triangulated-disc certificate (`DiskExpr`/`PlaneExpr`), because Mathlib has no planarity notion. It's arguable whether that equals graph planarity. | MED | **No.** devin-lai/jsp-000512-lean@60d55783 (2026-09-18, PR #922) uses a genuine `PlaneDrawing` (injective vertex points, continuous edge arcs with disjoint interiors that avoid vertices) and proves `IsLeast {k \| ∀ planar G, IsChoosable G k} 5`, plus a version for any vertex type. If plby's encoding is rejected, priority moves to devin-lai. |
| JSP-000198 (Erdős 216) | peilinliu66-dev/jsp-000198-lean | `erdos216_classification` gives g(3)=3, g(4)=5, g(5)=10, g(6) ≤ ES bound, and Horton counterexamples for k ≥ 7. Its README admits it **doesn't prove g(6)=30**, but the catalog cites HeSc24 (g(6)=30). | MED–HIGH | **Maybe in principle, blocked in practice.** g(6)=30 needs a huge SAT certificate. The 2024 Lean verification relied on an external checker and predates 2026. Not a realistic target. dcd PR maps it to E198, which is wrong (should be E216). |
| JSP-000078 (Erdős 58) | plby `Erdos58` | Challenge assumes `[Finite V]`; FC quantifies over arbitrary graphs. | MED | **No.** MaxwellLaw PR #130 / #2285 extends to arbitrary graphs, so priority moves to MaxwellLaw. |
| JSP-000733 (Erdős 882) | plby `Erdos882` | Proves only the lower bound `logb 2 n − 1 < maximumSize n`, not the asymptotic. | MED | **No.** PRs #31, #731, #4663, #5040 and claim #817 (zifanersuotang/erdos-882-lean) claim the full asymptotic. Priority belongs to whichever of these verifies first. |
| JSP-000506 (Erdős 625) | PR #363 ketianzhang1-lang (bridges at 2aca2f1, 2026-09-18) over SamPetkov/Erdos@824e4b6 (2026-08-30) | Statement `jsp_000506 : ∀ g, Tendsto (P[g ≤ χ − ζ]) atTop (𝓝 1)` matches the catalog. The PR is a **wrapper** around Petkov's proof, so the rules' original-repo/no-mirror priority goes to Petkov. dcd PR #3995 maps it to E506, which is wrong (should be E625). | MED (attribution) | **No.** Petkov's proof is complete and earlier. |
| JSP-000194 (Erdős 210) | plby `Erdos210` | Challenge theorem proves only `Tendsto ordinaryMinimum atTop atTop`. The linear bounds (`ten_mul_ordinaryCount_ge_card`, `ordinaryMinimum_upper`) are in the file but not in the challenge statement. | LOW–MED | No |
| JSP-000331 (Erdős 402) | plby `Erdos402` | Eventual form only, but the catalog asks "for sufficiently large", so it matches. `native_decide` only in lemmas the final theorem doesn't use. The header notes an axiom-free certificate for 7001..threshold is "remaining" (needed only for an explicit all-n version). | LOW | No. Competitors: kunjunsong #4831 is a non-Mathlib computational stub; #782 links an unrelated 637 repo. |
| JSP-001068, JSP-001071 | cadamcat (repos created 2026-10-14/15) | Full statements (atomic ionization `Statement`; homotopy hypothesis `Statement`) match the catalog. The screen had treated these as less saturated. | OK (build unverified) | No. Already claimed. |
| JSP-000027 (Artin) | cadamcat | Infinitude form, which is exactly what the catalog asks (density is listed as a "sharper form"). dcd maps it to E27, which is wrong. | OK | No |
| JSP-000035 (Catalan) | cadamcat | Four theorems using ℕ subtraction; equivalent to the catalog statement. | OK | No |
| JSP-000900 (distinct distances) | cadamcat | `jsp_000900`: lower bound c·\|P\|^{2/d} plus a matching upper bound. | OK | No |
| Hindman finite form, hypercube Ramsey (E181), E264, E821, E824 | cadamcat | Hypercube is FC `erdos_181` verbatim. Hindman is the finite sum-and-product form as cataloged. | OK | No |
| JSP-000029/164/166/171/263/312 | cadamcat | openai/math CONTENTS has no complete Lean link for these, so cadamcat's are the completing proofs. | OK | No. JSP-000168 also has a second claimant (#5075). |
| JSP-000183 (Erdős 193) | ekalvi/erdos-193 | Statement matches. dcd maps it to E183, which is wrong. | OK | No |

### Sampled plby statements that match (all OK, no reopen)

E4, E67, E69, E72, E133, E157, E163, E286, E292, E318 (disproof plus variants), E372, E421, E546 (disproof),
E549 (disproof), E586, E599, E730, E748, E763, E834, E946, E977, E999, E1010, E1105, E1124, E1149,
E1161, E1214, E1216. In each case the challenge theorem states the catalog's full claim: no extra hypotheses,
no finite truncation, and the correct quantifier order.

## Registration-layer problems (dcdreamy-code bulk PRs)

dcdreamy-code opened about 1000 "register plby proof" PRs, all open, as an editor rather than the author.
Under the rules ("do not register someone else's proof, a mirror or a copy on their behalf") these
cannot earn the Lean award for dcdreamy-code. Boris Alexeev / plby can still claim. Wrong targets we found:

| JSP | dcd points to | Actual source |
|---|---|---|
| 000027 | E27 | Artin (cadamcat) |
| 000035 | E35 | Catalan (cadamcat); PR closed |
| 000183 | E183 | E193 (ekalvi / plby) |
| 000198 | E198 | E216 (peilinliu) |
| 000204 | E204 | E227 |
| 000248 | E286 | E292 |
| 000391 | E391 | E482 |
| 000465 | E465 | E575 / E180 (openai) |
| 000506 | E506 | E625 (Petkov / PR #363) |
| 000512 | E512 | E631 |
| 000641 | E641 | E781 |
| 000658 | E803 | E801 |
| 000715 | E715 | E863 |
| 000748 | E748 | E900 |
| 000900 | E900 | distinct distances (cadamcat); PR closed |

Separately, awards issue #1017 (aichiwuhuarou) reports a pattern across third-party catalog-flip PRs:
16 restate local axioms, 36 derive from axiomatized literature, and 17 don't entail the theorem.
Drag0ndddd1118 acknowledged it for 79 PRs. Our grep found none of these problems in the plby files
behind our 294 entries. The issue is the registration PRs, not plby.

## Entries that may be reopened (none is a clean opening)

1. **JSP-000198.** The best public Lean proof omits g(6)=30, which the catalog's solution reference (HeSc24) establishes.
   Blocked: it needs a SAT-scale certificate in Lean.
2. **JSP-000320.** plby is conditional. The only unconditional proof (Collin, 0f6c715e) came through a PR
   that was closed over identity. If that author can't claim, the formalizer slot is arguably open, but a
   complete public proof already exists, so priority is unclear.
3. **JSP-000512.** Reopens only if both plby's certificate planarity *and* devin-lai's `PlaneDrawing`
   are rejected. Unlikely, since `PlaneDrawing` is the standard topological definition.

## Caveats

- Nothing was built; any claim could still fail to compile.
- GordonLtron's maintainer status is unverified.
- The plby ComparatorChallenges listing was assembled from the contents and tree APIs (631 files); a few may be missing.
- The statement comparison is a manual sample (about 45 entries), not exhaustive across all 287.
