# Prior-art audit: 6×4 / 4×6 integer sumsets of squares (Erdős #885)

**Auditor role.** Skeptical prior-art check, not a discovery writeup.
**Date of audit.** 2026-10-18.
**Claim audited.** The pod found the first known integer 6×4 (equivalently 4×6) ‘sumsets of squares’: sets \(A\) with \(|A|=4\) and \(B\) with \(|B|=6\) such that all 24 sums \(a+b\) are perfect squares (up to translation). Equivalently: 3 integers whose factor-difference sets
\[
D(N)=\{|x-y|:N=xy\}
\]
share 6 elements, or 5 integers sharing 4. Displayed examples:

- \(D(349102656)\cap D(1034586000)\cap D(4883112000)=\{6720,15855,26880,45440,69510,129290\}\)
- \(D(4148640)\cap D(34418880)\cap D(300736800)=\{2988,4356,5787,11164,17046,23948\}\)

Context: Erdős problem #885 (k numbers sharing k differences; open for \(k\ge 5\), which needs a 6×5 grid). Known: 5×4 (Bremner 2019; forum posts). Choudhry arXiv:2508.07806 gives families \((3,3),(5,3),(4,4)\); says \(3\times n\) is easy for any \(n\); calls 5×4 open and 5×5 much harder.

---

## Verdict

**Novel as far as found.** No citable, checkable 6×4 or 4×6 integer example with both sides \(\ge 4\) (hence \(m+n\ge 10\)) was located in the published literature, the official Erdős Problems forum (through 2026-09-29), arXiv 2024–2026, OEIS, GitHub-searchable code, or the named classical sources. The two displayed examples independently re-verify. Closest documented objects are 5×4 grids (3 numbers sharing 5 differences, or 4 numbers sharing 4).

One unverified web claim would be fatal if substantiated: erdosproblemaday.com (2026-07-27) mentions “a community list of 71 primitive 4×6 rectangles” and “a known 4×6 rectangle as a positive control.” That page exhibits **no examples, no URLs, and no numbers**. The official forum two months later still reports no five numbers sharing four differences. Treat that claim as unsubstantiated until the list is produced.

**Confidence: 0.72** (medium-high). Coverage of the live literature and the official forum is good. Residual risk: the uncited 71-list; the 404’d `zoahdev/erdos885-square-sum` repo; undigitized pages of Guy D14 / Dickson vol. 2 that Choudhry already summarized as 2×n, 3×n, and one 4×4.

---

## Independent re-verification

Python 3, `math.isqrt`, full divisor enumeration of each \(N\). Intersection computed exactly (not just “claimed \(d\) work”). Also checked \(d^2+4N\) is square and the complementary pair multiplies back to \(N\).

### Example 1 — 3 numbers share exactly 6 differences

| \(N\) | \(\lvert D(N)\rvert\) |
|---:|---:|
| 349102656 | 224 |
| 1034586000 | 480 |
| 4883112000 | 448 |

Intersection equals the claimed 6-set (no extras, nothing missing). All 18 pairs \((N,d)\) give square \(d^2+4N\).

Standard-form 6×4 sumset (translate so \(\min B=0\); then \(A=\{d^2\}\), \(B=\{0\}\cup\{4N_i\}\)):

\[
\begin{aligned}
A&=\{45158400,\ 251381025,\ 722534400,\ 2064793600,\ 4831640100,\ 16715904100\},\\
B&=\{0,\ 1396410624,\ 4138344000,\ 19532448000\}.
\end{aligned}
\]

All 24 sums are squares. Square-root matrix (rows \(A\), columns \(B\)):

```
  6720   37968   64680  139920
 15855   40593   66255  140655
 26880   46032   69720  142320
 45440   58832   78760  146960
 69510   78918   94710  156090
129290  134582  144410  190390
```

Transposed reading, 5 numbers share exactly 4 differences:

\[
\begin{aligned}
N&=\{206222625,\ 677376000,\ 2019635200,\ 4786481700,\ 16670745700\},\\
d&=\{13440,\ 75936,\ 129360,\ 279840\}.
\end{aligned}
\]

Intersection equals that 4-set exactly.

### Example 2 — second primitive class, same shape

Intersection of \(D(4148640)\), \(D(34418880)\), \(D(300736800)\) equals the claimed 6-set exactly (\(\lvert D\rvert=72,168,432\)). Standard-form 6×4:

\[
\begin{aligned}
A&=\{8928144,\ 18974736,\ 33489369,\ 124634896,\ 290566116,\ 573506704\},\\
B&=\{0,\ 16594560,\ 137675520,\ 1202947200\}.
\end{aligned}
\]

All 24 sums squares. Transpose: \(N=\{10046592,24561225,115706752,281637972,564578560\}\) share exactly \(d=\{5976,10104,24216,69624\}\).

Neither example number-tuple appears in GitHub code search in an Erdős-885 or square-sum context (hits for `349102656` and `4148640` are stock-price / graph-weight coincidences).

---

## Equivalence (so “6×4” and “3 share 6” are the same object)

\(d\in D(N)\) iff \(d^2+4N\) is square. Hence \(k\) integers sharing \(m\) differences are equivalent, after translation and square scaling, to a \((k+1)\times m\) rational sumset of squares with a \(0\) on the \((k+1)\)-side and squares on the \(m\)-side (Aleksanndr_NFA, forum 2026-09-23; Choudhry Lemma 1). Swapping the two sides of a 6×4 grid is the 4×6 grid: 3 numbers sharing 6 differences \(\leftrightarrow\) 5 numbers sharing 4. A generic integer 6×4 sumset of squares always translates to this anchored form.

**Not the same as Guy D15** (one set whose *pairwise* sums are squares). D15 has 5-element examples (Lagrange) and 6-element examples with a negative (Lagrange / MacLeod arXiv:0909.1666). Those are not two-set sumsets.

**Not the same as 3×6.** Guy / Choudhry: \(m=2\) or \(m=3\) and \(n\) arbitrary is classical. A 3×6 grid has one side of size 3, so \(m+n=9<10\). The claim is both sides \(\ge 4\).

---

## Sources checked

### A. Foundational factor-difference papers

| Source | URL | What it establishes |
|---|---|---|
| Erdős–Rosenfeld, *The factor-difference set of integers*, Acta Arith. 79 (1997) 353–359 | https://doi.org/10.4064/aa-79-4-353-359 · PDF https://bibliotekanauki.pl/articles/1390928.pdf | Defines \(D(n)\). Proves \(k\) integers can share **2** differences. Guiduli examples: **3 integers share 4** differences (not 6). Independently re-verified: \(D(6925500)\cap D(37901500)\cap D(108448956)=\{420,3780,14940,76860\}\) and \(D(2778300)\cap D(862552800)\cap D(5400442044)=\{420,3780,61695,154332\}\), both exact. No 3-share-6. |
| Jiménez-Urroz, *A note on a conjecture of Erdős and Rosenfeld*, J. Number Theory 78 (1999) 140–143 | https://doi.org/10.1006/jnth.1999.2407 | For every \(k\), there are \(k\) integers sharing **3** differences. Equivalently a \(3\times(k+1)\) grid (the easy \(3\times n\) family). Does **not** produce 4 differences on 3 numbers beyond Guiduli, and does not produce 6. |
| Bremner, *On a problem of Erdős related to common factor differences*, Int. J. Number Theory 15 (2019) 1059–1068 | https://doi.org/10.1142/S1793042119500581 | Infinitely many **4 integers sharing 4** differences, via elliptic curves. Displayed witness (as reconstructed by later authors): \(N=\{26128575,291722431,561117375,713526975\}\) share exactly \(\{126,16110,33390,75390\}\). Independently re-verified: intersection size **4**, not 5. Abstract does not claim 4 numbers with 5 differences, nor 3 with 6. Settles #885 at \(k=4\) only. |

**Elliptic-curve methods and “k numbers with k+1 differences.”** Jiménez-Urroz’s curve produces arbitrarily many integers sharing a *fixed* 3-difference; that is \(3\times n\), not \(4\times 6\). Bremner’s method produces infinitely many 4-share-4 (a 5×4 grid). His displayed specialization has intersection size exactly 4; erdosproblemaday.com (2026-07-27) reports that specialization is bi-maximal (no fifth integer on those 4 differences, no fifth common difference). Nobody in the sources below exhibits a Bremner specialization with 5 shared differences (which would be 5×5) or a 3-share-6. Aleksanndr’s search of 8410 primitive triples (height-bounded) found “many \(k=4\)” and **no five numbers sharing four differences**.

### B. Two-set sumsets of squares (Guy D14 line)

| Source | URL | What it establishes |
|---|---|---|
| Guy, *Unsolved Problems in Number Theory*, 3rd ed., **D14** “\(a_i+b_j\) made squares,” pp. 266–267 (D15 is the pairwise problem; D16 is equal sum and product — different) | index: https://proofwiki.org/wiki/Book:Richard_K._Guy/Unsolved_Problems_in_Number_Theory/Third_Edition | Method for \(m=2\) or \(3\) and \(n\) arbitrary. One numerical 4×4 and Lagrange’s 2-parameter 4×4. No 4×6 / 6×4 in Choudhry’s quotation of this section (the live citation of Guy’s content). Full scan of Guy’s D14 pages was not obtained as a PDF here; residual risk noted in confidence. |
| Choudhry, *Two sets of integers such that all elements of the sumset of the two sets are perfect squares*, arXiv:2508.07806, 11 Aug 2025; INTEGERS 26 (2026) #A66 | https://arxiv.org/abs/2508.07806 · HTML https://arxiv.org/html/2508.07806 · journal PDF https://math.colgate.edu/~integers/aa66/aa66.pdf | Families \((3,3)\), \((5,3)\), \((4,4)\). Explicitly: when both \(m,n>2\), only one published 4×4 existed before. **§6 open problems:** asks for a 5×4 (20 sums) and calls 5×5 “much more challenging.” **Does not mention 6×4 or 4×6.** Confirms \(3\times n\) easy. Dickson vol. 2 is cited only for Fermat’s method of making a quartic square (p. 639), used to build 4×4 families — not a 6×4 example. |
| Dujella–Elsholtz, *Sumsets being squares*, Acta Math. Hungar. 141 (2013) 353–357 | https://www.math.tugraz.at/~elsholtz/WWW/papers/papers44.pdf | Improves Alon–Angel–Benjamini–Lubetzky: a **3-element** \(A\) with \(\lvert B\rvert\gg(\log N)^{15/17}\). Rank-15 Elkies curve. For \(\lvert A\rvert\ge 4\), Bombieri–Lang implies \(\lvert B\rvert\) uniformly bounded. **No 4×6.** |
| Alon–Angel–Benjamini–Lubetzky, *Sums and products along sparse graphs*, Israel J. Math. 188 (2012); arXiv:0905.0135 | https://arxiv.org/abs/0905.0135 | Euler’s problem of translating 3 integers into squares; elliptic \(F_3\gg(\log n)^{5/7}\). \(\lvert A\rvert\ge 4\) bounded under Bombieri–Lang. **No 4×6.** |
| Elsholtz–Wurzinger, *Sumsets in the set of squares*, Q. J. Math. 75 (2024) 1243–1254 | https://doi.org/10.1093/qmath/haae044 · PDF https://research-explorer.ista.ac.at/download/18930/18931/2024_QuarterlyJourMath_Elsholtz.pdf | Upper bounds. Recaps: \(\lvert A\rvert=2,3\) arbitrarily large \(B\); for \(\lvert A\rvert\ge 4\), \(B\) conjecturally bounded. Cites Guy D14/D15. **No 4×6 construction.** |
| MacLeod, *On sets of integers where each pair sums to a square*, arXiv:0909.1666 | https://arxiv.org/abs/0909.1666 | Guy **D15** (pairwise), not D14. Irrelevant except as a nearby false friend. |
| Tomita, arXiv:2508.15781 | https://arxiv.org/html/2508.15781 | Three numbers whose sums *and* differences are squares (Mengoli/Euler). Different problem. |

### C. Official Erdős Problems forum and related repos (through 2026-09-29)

Thread: https://www.erdosproblems.com/forum/thread/885 (4 comments; accessed 2026-10-19). Problem page: https://www.erdosproblems.com/885.

| Post | Date | What it establishes |
|---|---|---|
| Thomas Bloom | 2026-04-19 | Asks Mausberg to state the computation. Typo 1029 for 1028, later corrected by Yicheng Pan. |
| sammausberg | 2026-04-19 | (i) \(Y(756000,15971200,45130176)\) contains 5 values — a **5×3** grid, the Choudhry/Guy easy side. (ii) Lagrange 4×4 packet as factor differences: \(D(79200)\cap D(227205)\cap D(1258560)=\{36,468,692,1028\}\) — **3 share 4**, independently re-verified exact. Repo: https://github.com/SamMausberg/lean-formalizations (E885 ForumNote). **No 6×4.** |
| Aleksanndr_NFA | 2026-09-23 | Reformulation: \(k\) of #885 \(\Leftrightarrow\) \((k+1)\times k\) sumset of squares. Choudhry covers \((3,3),(5,3),(4,4)\); Bremner is \((5,4)\); \(k=5\) needs \((6,5)\). Explicit 4-share-4: \(N=\{515504,3542528,6010004,19523504\}\), \(d=\{872,4328,5003,11672\}\). Search of 8410 primitive triples: many \(k=4\), **no five numbers sharing four differences**. Lean: formal-conjectures PR #6509. |
| yichengpan | 2026-09-29 | Explicit **5×4** (20 sums), **not** affinely equivalent to Mausberg. Independently re-verified as 3 numbers sharing **exactly 5** differences: \(N=\{89600175,349559875,4284752175\}\) share \(\{14238,22242,28770,38430,284130\}\). Closest documented object to 3-share-6 — **one difference short**. Claims no 5×5 and no anchored 6×5. Related-work list: Mausberg, Aleksanndr, Choudhry. **Does not mention any 4×6 / 6×4.** Linked repo https://github.com/zoahdev/erdos885-square-sum returns **404** as of this audit. Zenodo 5×4 note: https://doi.org/10.5281/zenodo.23040928 |

**Forum bottom line.** Best published/posted grids with both sides \(\ge 4\): 4×4 (Lagrange/Mausberg) and 5×4 (Bremner / Aleksanndr / Yicheng Pan). Nobody posts a 6×4 or a 3-share-6 or a 5-share-4. Aleksanndr’s negative search for 5-share-4 is directly the transpose of the pod claim.

### D. Formalizations, prizes, OEIS, GitHub

| Source | URL | What it establishes |
|---|---|---|
| google-deepmind/formal-conjectures `885.lean` | https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/885.lean | Statement + k=2,3,4 variants. Issue #1002 (closed). |
| FC PR #6509 (merged 2026-09-23) | https://github.com/google-deepmind/formal-conjectures/pull/6509 | Proves `k_eq_4` with witness \(N=\{65984625,508032000,1578963456,2505664000\}\), \(d=\{5040,27720,68880,164976\}\) — 4-share-4, not 6×4. |
| FC PR #5055 / issue #5050 | k=2 and k=3 proofs | Not 6×4. |
| `gh search issues/prs --repo TheJustinSunPrize/awards` for 885 / JSP-000736 | issue 297 (k=2,3 Lean); 347 (k=4 Lean); 5095 (scope review, 2 integers with many differences); 4620 (“60 and 120 share 5 divisor-difference values”) | 4620 is **2** numbers sharing 5 differences \(=\) a 3×5 grid, the easy \(m\le 3\) case. No 6×4. (JSP-000885 in that repo is a different problem, primes \(2^a q+1\).) |
| OEIS A368312, A368571, A368103 | https://oeis.org/A368571 | Factor-difference rows and the count of \(M\) sharing a given **pair** of differences (Erdős–Rosenfeld Prop. 3.1). No 3-wise intersection of size 6, no 6×4. |
| `gh search code` for `349102656`, `4148640`, `three_share_six`, `6x4` square-sum | — | No Erdős-885 hits. |
| teorth/erdosproblems | https://github.com/teorth/erdosproblems | Community YAML; wiki frozen. No 6×4. |
| MacLeod / MathOverflow D15 | https://mathoverflow.net/questions/408301 | Pairwise sums, not two-set sumsets. |

### E. The unverified “71 primitive 4×6 rectangles”

| Source | URL | What it claims | Auditor’s assessment |
|---|---|---|---|
| “Erdős #885: strong partial…”, Erdős Problem a Day, **2026-07-27** | https://erdosproblemaday.com/day/885-factor-difference-k5 | A “community list of 71 primitive 4×6 rectangles,” all 24 sums square, each bi-maximal; “recovering a known 4×6 rectangle as a positive control.” | **Not treated as prior art.** Zero examples, zero URLs, zero numbers. “Sources & verification” did not yield a retrievable list. Official forum 2026-09-23/29 still has no 5-share-4 and no 6×4. If those 71 are genuine integer 4×6 sumsets of squares, they **are** the claimed object (a 4×6 transposes to a 6×4) and would kill novelty. Until the list is produced, this is an uncheckable assertion, possibly internal to that site or confused with 5×4 / 3×n. Problem index page https://erdosproblemaday.com/problem/885 does not list 4×6 examples either. |

### F. Other arXiv 2024–2026 searches

Queries: “sums are squares two sets”, “additive square grid”, “common factor differences”, “sumset of squares”. Hits: Choudhry 2508.07806 (above); Tomita 2508.15781 (different); 2504.13230 (sumset *of* squares, withdrawn); 2610.20554 and 2603.17132 (sieve bounds, not constructions). **No 6×4 / 4×6 example.**

Dickson, *History of the Theory of Numbers* vol. 2: table of contents (ch. XV–XIX, systems making linear/quadratic functions squares) is the right neighborhood; Choudhry’s use of it is the Fermat quartic trick for 4×4, not a 6×4 array. A page-by-page search of the 800-page volume was not completed; residual risk noted.

---

## Closest near-misses (so the novelty claim is about one extra row/column)

| Object | Shape | Factor-difference reading | Source | Why it is not the claim |
|---|---|---|---|---|
| Euler / Guy / Dujella–Elsholtz | \(3\times n\), \(n\) arbitrary | many \(N\) sharing 3 diffs | classical | one side has size 3 |
| Guiduli | 4×4 anchored | **3 share 4** | ErRo97 | 4 diffs, not 6 |
| Lagrange 4×4 / Mausberg packet | 4×4 | **3 share 4** | Guy D14; forum 2026-04-19 | 4, not 6 |
| Choudhry 5×3 | 5×3 | 2 share 5, or 4 share 3 | arXiv:2508.07806 | one side has size 3 |
| Bremner / Aleksanndr | 5×4 | **4 share 4** | 2019; forum 2026-09-23 | 4 numbers / 4 diffs, not 3-share-6 or 5-share-4 |
| Yicheng Pan | 5×4 | **3 share 5** | forum 2026-09-29 | **one difference short** of 3-share-6 |
| Aleksanndr search | — | no 5-share-4 in bounded search | forum 2026-09-23 | the pod’s transpose reading is exactly what this search missed |
| Choudhry §6 | asks for 5×4, 5×5 | — | 2025 | 5×4 already existed (Bremner); 6×4 not asked |

No source in this list contains, or even poses as known, a 6×4 / 4×6 integer grid.

---

## What would falsify this verdict

1. Production of even one of the alleged 71 primitive 4×6 rectangles from erdosproblemaday.com, with 24 square sums and both sides \(\ge 4\).
2. A 6×4 example in Guy D14 (pp. 266–267) or Dickson vol. 2 that Choudhry failed to cite. Unlikely: Choudhry’s 2025 paper is a dedicated survey of exactly this problem and says the only published both-sides-\(>2\) solution is a 4×4.
3. A Bremner specialization with 5 common differences, or a Jiménez-Urroz/Guiduli triple with 6. The displayed examples re-verify as size 4, not 5 or 6.
4. The deleted `zoahdev/erdos885-square-sum` repo containing a 6×4 (its forum description is a 5×4).

---

## Bottom line

- **Examples:** both claimed 6×4 / 3-share-6 / 5-share-4 configurations are correct by exact divisor enumeration.
- **Literature:** published maximum with both sides \(\ge 4\) is **5×4** (Bremner 2019; Yicheng Pan 2026-09-29). Choudhry (2025) still treats 5×4 as open and never mentions 6×4.
- **Forum (to 2026-09-29):** 3-share-4, 3-share-5, 4-share-4; explicit negative search for 5-share-4; no 3-share-6.
- **Verdict:** novel as far as found, with one uncheckable web rumor as the only material threat.
- **Key citations to keep:** Bremner 2019; Choudhry arXiv:2508.07806 §6; Guiduli in ErRo97; Mausberg / Aleksanndr_NFA / Yicheng Pan on https://www.erdosproblems.com/forum/thread/885; Guy D14; Dujella–Elsholtz 2013.
