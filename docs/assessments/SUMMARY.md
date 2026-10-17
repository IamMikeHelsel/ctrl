# Bounty assessments — summary (20/20, 2026-10-17)

## Conclusion

All 20 shortlisted JSP problems are **NO-GO**. Every one already has a complete public Lean proof in plby/lean-proofs (Boris Alexeev), mostly first committed 2026-08-16..20. Two problems had proofs even earlier: JSP-000288, posted by Liam Price on the erdosproblems.com forum on 2026-06-19, and JSP-000731, in gotrevor/lean-gallery from 2026-06-28. Each problem also has between 5 and 30+ competing awards PRs, and most catalog entries are marked "Eligible to claim: No". No problem on this shortlist leaves room for an original, prize-eligible formalization. Per-problem effort estimates (S to XL) are moot. Every assessment met the 120 s per-problem time floor (minimum 242 s).

## Table

| JSP id | Erdős # | Verdict | Effort | Elapsed (s) | Existing proof (who, first date) | Awards PRs stated |
|---|---|---|---|---|---|---|
| JSP-000078 | 58 | NO-GO | XL | 252 | plby/lean-proofs, 2026-08-17 (finite graphs, ~524 files); MaxwellLaw arbitrary-graph extension, awards PR #130, 2026-09-16 | 8 PRs + 3 issues |
| JSP-000264 | 318 | NO-GO | S (parts.i) / XL (parts.ii) | 312 | plby/lean-proofs, 2026-08-16 (parts.i, contain_single_even, variants) | 9 (2 open, 7 closed) |
| JSP-000288 | 346 | NO-GO | M | 496 | Liam Price, erdosproblems.com forum, 2026-06-19 (~2150 lines); plby/lean-proofs, 2026-08-26 | 8 + claim issue #1218 |
| JSP-000307 | 372 | NO-GO | XL | 313 | plby/lean-proofs, 2026-08-17 | ~27 PRs/issues |
| JSP-000440 | 549 | NO-GO | M | 309 | plby/lean-proofs, 2026-08-17 (389 lines) | 6 |
| JSP-000490 | 603 | NO-GO | M | 256 | plby/lean-proofs, 2026-08-17 | 6 |
| JSP-000513 | 632 | NO-GO | L | 259 | plby/lean-proofs, 2026-08-17; three more repos 2026-09-16..17 | 8 + issue #16 |
| JSP-000603 | 735 | NO-GO | XL | 346 | plby/lean-proofs, 2026-08-20 (~150 modules) | 6 (incl. 1 withdrawn) |
| JSP-000672 | 815 | NO-GO | L | 345 | plby/lean-proofs, 2026-08-20 (2,085 lines) | 6 + issue #1020 |
| JSP-000688 | 832 | NO-GO | M | 242 | plby/lean-proofs, 2026-09-15 (936 lines); firesh/erdos832-lean, 2026-09-18 | 6 + 2 issues |
| JSP-000690 | 834 | NO-GO | S | 466 | plby/lean-proofs, 2026-08-17 (both readings) | 30+ PRs + ~12 issues |
| JSP-000731 | 880 | NO-GO | M | 307 | gotrevor/lean-gallery, 2026-06-28; plby/lean-proofs, 2026-08-17 | 7 |
| JSP-000733 | 882 | NO-GO | S | 281 | plby/lean-proofs, 2026-08-17 (lower bound) | ~12 + claim issue #817 |
| JSP-000751 | 903 | NO-GO | M | 269 | plby/lean-proofs, 2026-08-17 (1548 lines) | 8 |
| JSP-000760 | 916 | NO-GO | XL | 253 | plby/lean-proofs, 2026-08-20; Mizar77/jsp-000760-lean, 2026-09-18 | 7 + claim issue #1215 |
| JSP-000817 | 984 | NO-GO | L | 356 | plby/lean-proofs, 2026-08-18 (~6,900 lines) | 5 |
| JSP-001003 | 1198 | NO-GO | XL | 297 | plby/lean-proofs, 2026-08-17 (1698 lines) | 5 + issue #1174 |
| JSP-001007 | 1202 | NO-GO | M | 421 | plby/lean-proofs, 2026-08-17 | >10 PRs/issues |
| JSP-001010 | 1205 | NO-GO | M | 257 | plby/lean-proofs, 2026-08-17 | 7 |
| JSP-001021 | 1216 | NO-GO | L | 342 | plby/lean-proofs, 2026-08-17 | 13+ PRs + 8+ issues |

Time floor: 20/20 files present. All elapsed times are ≥ 120 s (range 242–496 s), and in every file end − start equals elapsed.

## Lessons for the next screen

- **(a) The catalog's "Lean proof: No" lags badly.** All 20 entries were marked "No", yet every one already had a complete public Lean proof, most of them about two months old.
- **(b) plby/lean-proofs covers nearly all solved Erdős problems.** Boris Alexeev's repo has 605 Erdős files, mostly committed 2026-08-17..26, and it contains all 20 problems here. Check `src/latest/ErdosProblems/Erdos<N>.lean` first.
- **(c) Awards PR counts are a fast saturation signal.** Searching `TheJustinSunPrize/awards` PRs for the JSP id found at least 5 PRs for every problem, and 30+ for JSP-000690. A count above zero should send the candidate to deep review or a reject.
- **(d) The screener underestimated proof size.** JSP-000817 was screened as a "short comment" but is ~6,900 Lean lines across ~50 files. JSP-000078 is ~524 files, JSP-000603 is ~150 modules, JSP-000288 is ~2150 lines and JSP-000672 is 2,085 lines. Existing formalization sizes are a better effort estimate than the length of the paper.
