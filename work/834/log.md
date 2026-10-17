# Log: Erdős 834

- 2026-10-17 · Claude Code (pilot). Picked 834 part ii over 1213/895/915/473/346/440: it is the only
  candidate whose whole proof is a finite, kernel-decidable witness check. Pulled Li's edge list from
  arXiv:2512.24850 (HTML, Section 4.1 / Appendix A). Re-checked it with a throwaway Python
  brute force: 22 edges, degrees [10,7×8], not 2-colourable, 3-colourable, every edge/vertex deletion
  2-colourable. The witness colourings were recomputed rather than copied.
- Wrote `lean/Challenge/Erdos834.lean` (verbatim FC part ii, `approved-by: (pending)`) and
  `lean/ErdosLab/Erdos834.lean`. All lemmas close by `decide +kernel` on the first try. The file
  compiles in about 50 s.
- `lean/scripts/check.sh 834`: build, tokens, axioms (propext, Classical.choice, Quot.sound) and
  binding all ok. Phase stays `draft` until a human approves the statement.
