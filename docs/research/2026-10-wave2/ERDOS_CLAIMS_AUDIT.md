# MATH06-AUDIT: priority-rescue audit of ctrl's "solved Erdős problems"

Lane MATH06-AUDIT, wave 2, 2026-10-24. Read-only audit: nothing was committed, pushed, posted or opened.
There is no Lean toolchain here, so no build in this report has been run. Every "sorry-free" below means
that `grep` found no `sorry`, `admit`, `axiom` or `native_decide` in the source. It does not mean the file builds.

## 0. Bottom line

* **The list.** The README headline says "25 solved". `docs/STATUS_AND_ROADMAP.md:22` and `docs/IDEA_PORTFOLIO_AND_SYNERGIES.md:102`
  list **29** numbers. The lane brief adds 291 and 382, which `ErdosBounties.lean` contains but the docs list omits, for **31**.
* **12 of the 31 numbers have no Lean anywhere in ctrl.** I checked every local and `origin/*` branch, the backup snapshots,
  `$C/ctrl-crossover`, `$C/ctrl-devsnapshot`, and `git log --all -G` over the full history of every `*.lean` file.
  The 12 are 36, 96, 242, 341, 389, 533, 995, 1055, 1059, 1073, 1102 and 1113, and none of them was ever formalized in ctrl.
  Seven of them (96, 242, 389, 995 main, 1055, 1059, 1073) are still **open** in Formal Conjectures (FC). Several match
  titles of *other people's* JSP PRs (36 #304, 242 #582, 389 #610, 995 #4655), so the docs list probably was assembled from JSP
  PR titles. **Remove all 12 from the docs.**
* **5 more are lemma-level only.** For 143, 275, 455, 873 and 1125, ctrl proves helper lemmas, not any FC statement.
* **No ctrl result is JSP-eligible.** Every ctrl proof of an FC *main* statement is already covered by someone else
  (plby, anatoliiohorodnyk, CYR, or around 30 JSP claimants for #834). Everything else is a variant, partial result or textbook lemma,
  which JSP rules exclude ("special cases, weaker results and conditional arguments do not qualify",
  `docs/assessments/CLAIM_AUDIT.md`, consistent with the JSP PR template's "fully solves the original problem").
* **What is left is small:** Formal Conjectures `formal_proof` links for **four** FC research-solved statements
  that ctrl proves exactly and that FC does not link yet: `erdos_834.parts.ii`, `erdos_1148.variants.weaker`,
  `erdos_367.variants.k_le_two` and `erdos_291.parts.ii`. Others hold priority on 291 and 834, so those links earn
  FC credit only. One Palomar entry (834.ii) is plausible.

Verdict counts (31 numbers): **RESCUE NOW 3** (834, 1148, 367) · **already scooped 7** (261, 291, 370, 493, 645, 1179, 1187) ·
**variant only 4** (311, 382, 931, 951) · **not actually proved 17** (12 with no Lean, 5 lemma-only) · **needs glue proof 0**.
#291 is "already scooped", but its FC link is still open as an optional fourth FC PR.

### Corrections to wave 1 / BOUNTIES.md top block
1. "#291 and #367 were formalized by plby since 10-17" is **inaccurate**.
   * plby only has `Erdos291b`, a *conditional* generalization tagged `partial: yes` with the conditions `h_priemteller` and `h_bla0`.
   * plby's `Erdos367`/`Erdos367b` is the k=3 *disproof*, roughly parts.ii in its own definitions.
   * Neither is ctrl's statement. 291 part (ii) **is** already formalized publicly, but by Collin Yuanjie Ren (CYR).
     The erdosproblems.com note was dated 2026-06-24. Source: the ctrl research-notebook snapshot `erdos-problems.yaml`, and JSP PR #216, closed.
2. "#261 (Palomar)" is confirmed: FC `261.lean` header cites `PALOMAR-2026-10-11-000016`. `parts.i` links anatoliiohorodnyk.
3. "The repo is private" is **no longer true**. `https://api.github.com/repos/IamMikeHelsel/ctrl` returned
   `"private": false, "visibility": "public"` today (created 2026-10-17, pushed 2026-10-24). When it became public
   is unknown, and that date matters for JSP priority, which goes to the earliest *public* commit.
4. "14 still-unlinked formalizations" is really **4**, listed above.
5. Local `main` is 47 commits behind `origin/main`. Local main lacks `erdos/`, which is on `origin/main` (124e2f7). Pin to `origin/main`.
   The working branch also moved mid-audit (HEAD 344734e). The audit used the refs as fetched.

## 1. Method and sources

* ctrl refs: all 48 `refs/remotes/origin/*` and the 2 local heads, via
  `git grep -E "(Erd[őo]s[ _#]*(Problem )?#?N\b|[Ee]rdos_?N\b|ErdosN\b|ErdosProblems/N\.lean)" <ref> -- '*.lean'`.
  A second, looser pass (`#N`, `_N`, `N.lean`, `Problem N`) turned up only false positives, such as `node_995` in a covering-tree certificate.
  History check: `git log --all -G'(erdos_N\b|ErdosN\b|Erdős #N\b)' -- '*.lean'`, which was empty for all 12 missing numbers.
  Raw hit list: `(session scratch file, not committed)`.
* FC: `$C/formal-conjectures` @ `c094b979118b89adb77cf5f8d923ac9dd2e51b1d` (2026-10-23). The parser is at
  `(session scratch file, not committed)`.
  Its theorem counts were cross-checked against `grep -c '^theorem'`.
* plby: `$C/plby-lean-proofs` @ `8822f7ddef30fadbd92e1c6ab4ed897af356af5e` (shallow; 574 `sources.yaml` keys).
* JSP: `ctrl/tools/data/jsp_erdos_map.json`, `jsp.json`, `awards_prs.json` (snapshots of 2026-10-17; 4,474 PRs; no author field).
  I could not fetch PR authors: the GitHub API refused this repo for the session, and I did not call `add_repo`.
  JSP `docs/award-process.md` and `.github/PULL_REQUEST_TEMPLATE.md` were fetched from raw.githubusercontent.com
  into `scratchpad/wave2/math06/jsp/`.
* Palomar: palomar-registry.org is blocked. The only Palomar IDs used here are those cited in FC files.
  Of the 31 numbers, only 261 has one. The `formalization.yaml` format was taken from plby `src/latest/ErdosProblems/Erdos730/formalization.yaml` (schema v0.4).

## 2. Master table

Column meanings:
* **sf?** = sorry-free by grep.
* **FC main?** = whether ctrl proves the FC *main* statement exactly (I = identical, G = equivalent with glue, V = an FC variant or part, L = a lemma that is not an FC statement, — = nothing).
* **FC fp** = who holds the `formal_proof` link on the FC statement ctrl targets, with the main statement's link in brackets.
* **plby** = the `sources.yaml` key or file for that problem.

Ref abbreviations:
* **OM** = `origin/main` @ `124e2f7787e31cf24f39e1a7b3bf37bf79a93df2` (also local main and claude/pensive-fermat-ktzrcs for the `ControlsLean/Bounty` files).
* **ELS** = `origin/backup/20261020/dev-ctrl-erdos-lab/snapshot` @ `c291008b20018ed778500356a81ad56b44fe5519`.
* `EB` = `ControlsLean/Bounty/ErdosBounties.lean`, `NI` = `ErdosNewInsights.lean`, `W2` = `ErdosWave2.lean`.
* `EL/N` = `erdos/ErdosLab/ErdosN.lean` together with `erdos/Challenge/ErdosN.lean`. These are FC-import Challenge/Solution pairs pinned to FC `d9ce556`.

| # | ctrl location (ref: file → theorem) | sf? | FC main? | FC fp (target / [main]) | plby | Palomar | JSP | verdict | next action |
|---|---|---|---|---|---|---|---|---|---|
| 36 | none in any ref or history | – | – | [main open; lower/upper variants → linrock] | no | – | JSP-000065 Open; others' PRs #304/#2586/#3039 closed | not actually proved | delete from docs |
| 96 | none | – | – | [main `erdos_96` **open**] | no | – | JSP-000110 Open; #4283, #289 open (others) | not actually proved | delete from docs |
| 143 | OM: EB → `erdos_143_ncard_le_floor`, `_floor_injOn`, `_one_separated` (also in backups and lean/ControlsLean) | yes | L (parts.i and ii both **open**) | – | no | – | JSP-000145 Open; #722 closed | not actually proved | delete from "solved" list |
| 242 | none | – | – | [main **open** (Erdős–Straus)] | no | – | JSP-000213 Open; #4596, #3479 open | not actually proved | delete |
| 261 | OM: EB → `erdos_261_parts_i`, `_borwein_loring(_property)`; OM: EL/261 → `Challenge.Erdos261.solution` (FC import) | yes | V-I: `parts.i` identical (FC main also has parts.ii/iii, both **open**) | `parts.i` → anatoliiohorodnyk/lean-fc-proofs; variants → linrock | no | **PALOMAR-2026-10-11-000016** (third party) | not in JSP | already scooped | none |
| 275 | OM: NI → `erdos_275_extremal_sharpness`, `_dyadic_covers_Icc` | yes | L (sharpness example, not the Crittenden–Vanden Eynden theorem) | [main → plby] | yes | – | not in JSP | not actually proved | delete |
| 291 | OM: EB → `erdos_291_parts_ii` (standalone, defs verbatim); **ELS only**: EL/291 → `Challenge.Erdos291.solution` (FC import) | yes | V-I: `parts.ii` identical (part i **open**) | `parts.ii`: **none** | `Erdos291b` only (conditional generalization, `partial: yes`) | – | JSP-000247 Open; #216 closed (same result); **CYR public Lean ≈2026-06-24** | already scooped (CYR); FC link still open | optional FC PR (§4.4) after landing EL/291 on main |
| 311 | OM: W2 → `Erdos311.delta_ge_inv_lcm`, `delta_one` | yes | V (FC `textbook` lemma; main **open**) | – (FC body `sorry`) | no | – | JSP-000260 Open; #480 closed (same lemma) | variant only | optional FC inline-proof PR (≈45 lines, at FC's length limit); no JSP or Palomar |
| 341 | none | – | – | [main → plby] | yes | – | not in JSP | not actually proved | delete |
| 367 | OM: W2 → `Erdos367.erdos_367.variants.k_le_two` (standalone, `B` verbatim) | yes | V-I: `variants.k_le_two` identical (parts.i **open**; parts.ii solved by others) | `k_le_two`: **none** [`higher_full_parts` → kusasyu36] | `Erdos367` (k=3 disproof), `Erdos367b` partial | – | JSP-000303 Open; #455 closed ("trivial k ≤ 2 bound", other author); #4278 open | **RESCUE NOW** (FC variant link only) | §4.3 |
| 370 | OM: NI → `erdos_370` (local `maxPrimeFac`, verbatim FC def) | yes | I | [main → plby **and** XC0R] | yes | – | not in JSP | already scooped | none |
| 382 | OM: EB → `erdos_382_lt_two_mul_of_largestPrimeRepeated` (explicit-p form, needs glue); **ELS only**: EL/382 (FC import) | yes | V (FC `textbook`, **already proved inline in FC**); parts.i/ii **open** | n/a | no | – | not in JSP | variant only | none |
| 389 | none | – | – | [main **open**] | no | – | JSP-000322 Open | not actually proved | delete |
| 455 | OM: W2 → `Erdos455.discreteConvex_*` | yes | L (main **open**; liminf > 0.352 variant not proved) | – | no | – | not in JSP | not actually proved | delete |
| 493 | OM: NI → `erdos_493` | yes | I (FC statement is trivially true with k=2) | [main → plby] | yes | – | not in JSP | already scooped | none |
| 533 | none | – | – | [main → plby] | yes | – | not in JSP | not actually proved | delete |
| 645 | OM: NI → `erdos_645` | yes | I | [main → plby] | yes | – | not in JSP | already scooped | none |
| 834 | OM: **EL/834 → `Challenge.Erdos834.solution`** (FC import; first commit 4a94d15, 2026-10-17); OM: EB → `erdos_834_parts_ii` (own defs) | yes (`decide +kernel`) | V-I: `parts.ii` identical (FC has no single main; `parts.i` is the other reading) | `parts.ii`: **none**; `parts.i`: none | `Erdos834` (both readings, own defs) | none known | JSP-000690 **Solved, eligible No**, ≈30 claim PRs | **RESCUE NOW** (FC link + Palomar candidate; JSP scooped) | §4.1 |
| 873 | OM: NI → `erdos_873_lcm_ge_add` | yes | L (main **open**) | [`supplement_all_scale` → KitaKen1] | no | – | not in JSP | not actually proved | delete |
| 931 | OM: EB and EL/931 → `additional_condition_nonempty` (FC import) | yes | V (main **open**; variant **already proved inline in FC** with AlphaProof's witness) | n/a | no | – | JSP-000773 Open; #294 closed | variant only | none |
| 951 | OM: EB → `erdos_951_isBeurlingPrimes` (local defs) | yes | V (FC `API` lemma, **already proved inline**); main **open** | n/a | no | – | not in JSP | variant only | none |
| 995 | none | – | – | [main **open**; lower-bound variant unlinked] | no | – | JSP-000828 Open; #4655 open (other) | not actually proved | delete |
| 1055 | none | – | – | [main **open**] | no | – | not in JSP | not actually proved | delete |
| 1059 | none | – | – | [main **open**] | no | – | not in JSP | not actually proved | delete |
| 1073 | none | – | – | [main **open**] | no | – | not in JSP | not actually proved | delete |
| 1102 | none | – | – | [4 solved parts → Woett] | yes | – | not in JSP | not actually proved | delete |
| 1113 | none | – | – | [main **open**; Sierpiński variant → HowieHwong] | no | – | not in JSP | not actually proved | delete |
| 1125 | OM: NI → `erdos_1125_kemperman_le_max`, `_monotone_chain` | yes | L (the main `Monotone f` is not proved) | [main → plby] | yes | – | not in JSP | not actually proved | delete |
| 1148 | OM: W2 → `Erdos1148.erdos_1148.variants.weaker` (standalone, defs verbatim) | yes | V-I: `variants.weaker` identical (main proved by plby) | `weaker`: **none** [main → plby] | main only (`Erdos1148`, no weaker) | – | JSP-000953 Solved, Lean Yes (plby) | **RESCUE NOW** (FC variant link only) | §4.2 |
| 1179 | OM: W2 → `Erdos1179.erdos_1179.variants.lower_bound` | yes | V-I (identical defs/statement) | `lower_bound` → plby (L3564) | yes | – | not in JSP | already scooped | none |
| 1187 | OM: W2 → `Erdos1187.erdos_1187.parts.ii` (local `IsAPOfLengthWith`, verbatim FC def) | yes | V-I: `parts.ii` identical | `parts.ii` → plby | yes | – | JSP-000992 Solved, eligible No; #689 closed | already scooped | none |

ctrl also contains Erdős-tagged Lean for 667 (only `findGreatest_mono_pred`, not an FC statement), 885 and 273 (crossover research
branch, out of scope here).

## 3. Statement comparisons (FC @ c094b97 vs ctrl), for the numbers with real ctrl Lean

Each pair below was checked character by character against the FC source.

* **834 parts.ii.**
  * FC: `∃ (n : ℕ) (H : Finset (Finset (Fin n))), H.IsUniform 3 ∧ H.HasHypergraphChromaticNumber 3 ∧ (∀ e ∈ H, (H.erase e).HypergraphColorable 2) ∧ (∀ v : Fin n, (H.filter (fun e ↦ v ∉ e)).HypergraphColorable 2) ∧ ∀ v : Fin n, 7 ≤ H.hypergraphDegree v`.
  * ctrl `erdos/Challenge/Erdos834.lean` `def statement` is the same text, importing `FormalConjectures.ErdosProblems.«834»` @ d9ce556.
  * The FC-for-Mathlib definitions at c094b97 (`Finset.IsProperHypergraphColoring`, `HypergraphColorable`, `HasHypergraphChromaticNumber`,
    `hypergraphDegree`, in `FormalConjecturesForMathlib/Combinatorics/Hypergraph/Finite.lean`) have the shape the ctrl proof unfolds.
  * **Identical.** The ControlsLean `erdos_834_parts_ii` re-declares the definitions locally (equivalent with glue), so use the `erdos/` version.
* **1148 variants.weaker.**
  * FC: `theorem erdos_1148.variants.weaker : ∀ n, erdos_1148_weaker_prop n`, with
    `def erdos_1148_weaker_prop (n : ℕ) : Prop := ∃ x y z : ℕ, n = x ^ 2 + y ^ 2 - z ^ 2 ∧ (x ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n ∧ (y ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n ∧ (z ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n`.
  * ctrl W2:104: `theorem erdos_1148.variants.weaker : ∀ n : ℕ, erdos_1148_weaker_prop n`, with a character-identical local definition.
  * **Identical** modulo namespace, but standalone: it does not import FC.
  * The argument is sound. Write n = m² + r. If r is odd, take (m, k+1, k). If r = 0, take (m, 0, 0). If r = 2k ≥ 2, take (m+1, m−k, m−k+1).
* **367 variants.k_le_two.**
  * FC: `∀ k : ℕ, k ≤ 2 → (fun n ↦ ((∏ m ∈ .Ico n (n + k), B 2 m : ℕ) : ℝ)) =O[atTop] fun n ↦ (n : ℝ) ^ (2 : ℝ)`.
  * ctrl W2:412: the same statement, with `Finset.Ico` written in full and a verbatim `B`.
  * **Identical** modulo namespace, standalone. Mathematically trivial: B₂(m) ≤ m.
* **291 parts.ii.**
  * FC: `{ n : ℕ | Nat.gcd (a n) (L n) > 1 }.Infinite`, with `L n = (Finset.Icc 1 n).lcm (fun x ↦ x)` and `a n = ∑ k ∈ Finset.Icc 1 n, L n / k`.
  * ctrl ELS `erdos/Challenge/Erdos291.lean` has the same text (FC import).
  * ctrl EB:527 `{ n : ℕ | Nat.gcd (erdos291A n) (erdos291L n) > 1 }.Infinite` uses verbatim local definitions.
  * **Identical.**
* **261 parts.i.** FC `{n : ℕ | 0 < n ∧ Erdos261Prop n}.Infinite`, the same as EL/261 `statement`. **Identical**, already linked by others.
* **370.** FC `{ n | Nat.maxPrimeFac n < √n ∧ Nat.maxPrimeFac (n + 1) < √(n + 1) }.Infinite`. ctrl's
  `{ n : ℕ | (maxPrimeFac n : ℝ) < Real.sqrt n ∧ (maxPrimeFac (n + 1) : ℝ) < Real.sqrt (n + 1) }.Infinite` uses a local `maxPrimeFac`
  that has the same body as FC's `Nat.maxPrimeFac`. **Identical** after unfolding.
* **493, 645.** Identical to the FC main statements, which are already linked to plby.
* **1179 lower_bound, 1187 parts.ii.** Identical. FC links plby for both.
* **931 additional_condition_nonempty, 951 isBeurlingPrimes, 382 lt_two_mul_of_largestPrimeRepeated.** Identical to FC statements,
  but FC **already contains inline proofs** of all three (AlphaProof's (10,3,0,13) witness, the API proof, and the textbook proof). Nothing to link.
* **311 delta_ge_inv_lcm.** Identical; FC body is `sorry`, category `textbook`.
* **143, 275, 455, 873, 1125.** ctrl's theorems are **not** FC statements:
  * 143: `(A ∩ Icc 1 x).ncard ≤ ⌊x⌋₊`, against FC's open `liminf … = 0` and `Summable`.
  * 275: dyadic sharpness, against FC's covering theorem.
  * 455: convexity growth lemmas, against FC's `Tendsto (q n / n²) atTop atTop` and the liminf > 0.352 variant.
  * 873: lcm ≥ i+k, against FC's `F a X k < X^ε`.
  * 1125: a greedy chain lemma, against FC's `Monotone f`.

## 4. RESCUE NOW drafts (not submitted)

Shared preconditions:
* The repo is now public. Verify that before relying on it.
* Pin full 40-character SHAs that are reachable from a public branch.
* Sign the Google CLA, which FC requires.
* Disclose AI assistance per Mathlib's AI policy, which FC follows.
* Bump `erdos/lakefile.toml` from FC `d9ce556` to the FC head (`c094b97` uses the same `leanprover/lean4:v4.33.1` and mathlib `v4.33.1`),
  rebuild, and pin the SHA *after* that rebuild. That way the linked proof is checked against the statement FC currently has.

### 4.1 Erdős 834 parts.ii (best item)

**FC PR.** File: `FormalConjectures/ErdosProblems/834.lean`, line 59 at c094b97.
```diff
-@[category research solved, question, AMS 5]
+@[category research solved, question, AMS 5, formal_proof using lean4 at
+  "https://github.com/IamMikeHelsel/ctrl/blob/124e2f7787e31cf24f39e1a7b3bf37bf79a93df2/erdos/ErdosLab/Erdos834.lean#L81"]
 theorem erdos_834.parts.ii :
```
Replace `124e2f7…` with the SHA after the FC-pin bump if one happens. The earliest commit holding identical content is
`4a94d150be60ffa60f726ebcc7c13b9220966de0` (2026-10-17, `lean/ErdosLab/Erdos834.lean`, on the backup branches).

PR title: `Erdős 834: add formal_proof link for parts.ii`. Body:
> Adds a `formal_proof` link for `erdos_834.parts.ii`. The linked file proves `Challenge.Erdos834.statement`, which is the
> FC statement copied verbatim; the Challenge module imports `FormalConjectures.ErdosProblems.«834»` (pinned FC commit in
> `erdos/lakefile.toml`). The witness is R. Li's 9-vertex, 22-edge 3-uniform hypergraph [Li25, §4.1]. All finite facts are
> checked by kernel `decide +kernel`. Axioms: propext, Classical.choice, Quot.sound. AI-assisted formalization, reviewed by
> the author. (Independent formalization in different definitions: plby/lean-proofs `ErdosProblems/Erdos834`.)

**Palomar `formalization.yaml` stub.** This needs repackaging first: a Mathlib-only `Challenge.lean`, the `module` system, and a comparator config.
```yaml
# yaml-language-server: $schema=https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/main/schema/formalization.schema.json
version: "v0.4"
project:
  name: "ctrl Erdős lab: Erdős Problem #834 (part ii)"
  description: >-
    Kernel-checked proof that there exists a 3-uniform hypergraph with weak chromatic number 3, minimum
    degree at least 7, that becomes 2-colourable after deleting any edge or any vertex (Erdős–Lovász,
    erdosproblems.com/834, chromatic reading). Witness: R. Li's explicit 9-vertex, 22-edge hypergraph.
  authors: ["Mike Helsel"]
  responsible_maintainers: ["Mike Helsel"]
  license: "Apache-2.0"
sources:
  - title: "R. Li, On an Erdős-Lovász problem: 3-critical 3-graphs of minimum degree 7, arXiv:2512.24850 (2025)"
    authors: ["R. Li"]
    id: "https://arxiv.org/abs/2512.24850"
    type: "paper"
    location: "Section 4.1 (explicit hypergraph)"
    relationship: "formalizes"
    author_endorsement: "not-contacted"
  - title: "Formal statement erdos_834.parts.ii in Formal Conjectures"
    authors: ["The Formal Conjectures Authors (Google DeepMind)"]
    id: "https://github.com/google-deepmind/formal-conjectures"
    type: "other"
    location: "FormalConjectures/ErdosProblems/834.lean"
    relationship: "background"
    license: "Apache-2.0"
    author_endorsement: "n/a"
related_formalizations:
  - id: "https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos834.md"
    relationship: "other"
    note: "Independent formalization of both readings in its own definitions."
classification:
  arxiv: ["math.CO"]
  msc2020: ["05C65", "05C15"]
status:
  scope: "Complete proof of the chromatic reading (FC parts.ii) only."
  sorry_count: 0
  sorry_in_definitions: 0
  axioms: ["propext", "Classical.choice", "Quot.sound"]   # VERIFY with #print axioms
  main_results:
    - declaration: "Palomar.Erdos834.erdos_834_parts_ii"   # TODO after repackaging
      file: "TODO"
      sorry_count: 0
      axioms: ["propext", "Classical.choice", "Quot.sound"]
      comparator_config: "TODO"
      literature_dependencies: []
automation:
  methods:
    - method: "agent"
      models: []            # TODO: fill from session records
      framework: "TODO (Claude Code / Spark prover sessions per commit messages)"
  spend_usd: "not recorded"
fidelity:
  divergences: "None in the statement: FC parts.ii copied verbatim. The transversal reading (parts.i) is not covered."
review:
  status: "self-assessed"
  reviewers: []
alignment:
  namespace: "Palomar"
  statements:
    - source: "Erdős #834 (chromatic reading): 3-critical 3-uniform hypergraph with min degree ≥ 7"
      lean: "Palomar.Erdos834.erdos_834_parts_ii"
      module: "Palomar.Erdos834.Challenge"
      status: "proved"
```
Palomar risk: plby or a JSP claimant may already have registered 834. I could not check because palomar-registry.org is blocked.

**JSP legacy PR body. Recommendation: DO NOT FILE.** JSP-000690 is "Solved", with "Eligible to claim: No" and about 30 prior claim PRs,
and ctrl's commit (2026-10-17) is later than many of them. If it is filed anyway, it should be a no-priority reference only:
```
## Problem
- Problem ID(s): JSP-000690
- Original problem source and exact location: https://www.erdosproblems.com/834 (chromatic reading)
- Current entry and proposed change: none; independent formalization reference, no priority claim
- Related PRs and how this contribution differs: see #1609, #1613, #4071 and others; this proof targets the
  Formal Conjectures statement `Erdos834.erdos_834.parts.ii` verbatim via an importing Challenge module
## Formal statement
- Complete mathematical solution: R. Li, arXiv:2512.24850, §4.1
- Formal statement location, pinned: https://github.com/IamMikeHelsel/ctrl/blob/<SHA>/erdos/Challenge/Erdos834.lean
- Fully qualified target theorem name: Challenge.Erdos834.solution
- Statement origin: Formal Conjectures `erdos_834.parts.ii` @ <FC SHA> (verbatim)
- Correspondence: identical text; covers only the chromatic reading
## Proof submission
[{"repository": "https://github.com/IamMikeHelsel/ctrl", "branch": "main", "commit": "<40-char SHA>"}]
- Proof file and theorem: erdos/ErdosLab/Erdos834.lean, Challenge.Erdos834.solution
## Reproduction
- Lean: leanprover/lean4:v4.33.1 (erdos/lean-toolchain); deps: erdos/lake-manifest.json (formal_conjectures, mathlib v4.33.1)
- Commands: see §5; axiom audit: `#print axioms Challenge.Erdos834.solution`
## Attribution
- Mathematical solver: R. Li. Lean formalization: Mike Helsel (AI-assisted). No priority claim.
```

### 4.2 Erdős 1148 variants.weaker

**Port first.** This step is recommended so that the proof is bound mechanically to FC's definitions. Add
`erdos/Challenge/Erdos1148.lean`:
```lean
import FormalConjectures.ErdosProblems.«1148»

/-!
# Challenge: Erdős Problem 1148 (variants.weaker)

Statement copied verbatim from `Erdos1148.erdos_1148.variants.weaker` in
FormalConjectures.ErdosProblems.«1148» (google-deepmind/formal-conjectures @ <FC SHA>, Apache-2.0).
Source: https://www.erdosproblems.com/1148
-/

open Erdos1148

namespace Challenge.Erdos1148

/-- statement copied from FormalConjectures.ErdosProblems.«1148» `erdos_1148.variants.weaker`
(Apache-2.0) -/
def statement : Prop :=
    ∀ n, erdos_1148_weaker_prop n

-- approved-by: (pending)

end Challenge.Erdos1148
```
Then add `erdos/ErdosLab/Erdos1148.lean`:
* `import Challenge.Erdos1148`, `open Erdos1148`, `namespace Challenge.Erdos1148`.
* Copy W2 lines 74–98 verbatim as `private theorem`s: `erdos_1148_prop_of_sq_eq`, `_of_odd_rem` and `_weaker_of_strong`.
  They only mention `Erdos1148Prop` and `erdos_1148_weaker_prop`, which now resolve to FC's identical definitions.
* Add `theorem solution : statement := by` followed by the body of W2 lines 105–152, starting at `intro n`.
* Register both files in `erdos/Challenge.lean` and `erdos/ErdosLab.lean`.

Risk: W2 was written against Mathlib `v4.36.0-rc1` (root lakefile), while `erdos/` uses `v4.33.1`. Lemma names such as
`Nat.sqrt_le'`, `Nat.lt_succ_sqrt'` and `Real.sqrt_le_sqrt` must be re-checked at build time.

**FC PR.** File: `FormalConjectures/ErdosProblems/1148.lean`, line 93.
```diff
-@[category research solved, AMS 11]
+@[category research solved, AMS 11, formal_proof using lean4 at
+  "https://github.com/IamMikeHelsel/ctrl/blob/<SHA-after-port>/erdos/ErdosLab/Erdos1148.lean#L<solution line>"]
 theorem erdos_1148.variants.weaker : ∀ n, erdos_1148_weaker_prop n := by
```
No-port fallback, which links the standalone copy with verbatim definitions:
`https://github.com/IamMikeHelsel/ctrl/blob/852a26adf82b8f5daa437e30c4e35bc486154867/ControlsLean/Bounty/ErdosWave2.lean#L104`.
Alternatively, the proof is about 80 lines with its helpers, above FC's 25–50-line inline limit, so the link is the right channel.

**Palomar stub.** Same skeleton as §4.1, with these fields changed:
* `sources`: [Va99] "Some of Paul's favorite problems" (1999), relationship `formalizes`. Erdős–Vaughan called this variant "obvious".
* `fidelity`: "variant only; main erdos_1148 not covered".

**Recommendation: do not submit to Palomar.** This is below the research-interest floor.

**JSP legacy PR. DO NOT FILE: not eligible.** JSP-000953 is the *main* problem, already Solved with plby's Lean recorded.
A weaker variant does not "fully solve the original problem" (template checklist item 2). If it were ever relevant, the
template fields would be: Problem ID JSP-000953; target `Challenge.Erdos1148.solution`; solver credit to the statement in [Va99];
formalizer Mike Helsel (AI-assisted); "Correspondence: proves FC `erdos_1148.variants.weaker`, NOT the main statement".

### 4.3 Erdős 367 variants.k_le_two

**Port.** Add `erdos/Challenge/Erdos367.lean`:
```lean
import FormalConjectures.ErdosProblems.«367»

/-!
# Challenge: Erdős Problem 367 (variants.k_le_two)

Statement copied verbatim from `Erdos367.erdos_367.variants.k_le_two` in
FormalConjectures.ErdosProblems.«367» (google-deepmind/formal-conjectures @ <FC SHA>, Apache-2.0).
Source: https://www.erdosproblems.com/367
-/

open Erdos367 Asymptotics Filter

namespace Challenge.Erdos367

/-- statement copied from FormalConjectures.ErdosProblems.«367» `erdos_367.variants.k_le_two`
(Apache-2.0) -/
def statement : Prop :=
    ∀ k : ℕ, k ≤ 2 →
    (fun n ↦ ((∏ m ∈ .Ico n (n + k), B 2 m : ℕ) : ℝ)) =O[atTop]
      fun n ↦ (n : ℝ) ^ (2 : ℝ)

-- approved-by: (pending)

end Challenge.Erdos367
```
Then add `erdos/ErdosLab/Erdos367.lean`:
* Copy W2 `B_dvd`, `B_le_self`, `prod_B_le_prod_Ico` and `prod_B_two_le_two_mul_sq` as private lemmas about FC's `B`, which has an identical body.
* Add `theorem solution : statement := by` with the body of W2 lines 415–426.

**FC PR.** File: `FormalConjectures/ErdosProblems/367.lean`, line 68.
```diff
-@[category research solved, AMS 11]
+@[category research solved, AMS 11, formal_proof using lean4 at
+  "https://github.com/IamMikeHelsel/ctrl/blob/<SHA-after-port>/erdos/ErdosLab/Erdos367.lean#L<solution line>"]
 theorem erdos_367.variants.k_le_two : ∀ k : ℕ, k ≤ 2 →
```
No-port fallback: `…/blob/852a26adf82b8f5daa437e30c4e35bc486154867/ControlsLean/Bounty/ErdosWave2.lean#L412`.

Better alternative: the whole proof is about 40 lines and trivial, so offer it as an **inline FC proof** replacing `sorry`.
CONTRIBUTING.md welcomes "very short proofs for solved items".

Caveat: JSP PR #455 (closed) titled "Lean proof of the trivial k ≤ 2 bound" suggests someone else has an earlier public proof.
I could not identify the author.

**Palomar.** Do not submit; this is trivial and below the floor. Stub as in §4.2 if wanted.

**JSP. DO NOT FILE: not eligible.** JSP-000303's main problem (parts.i) is open, and a special case does not qualify.

### 4.4 Erdős 291 parts.ii (optional; priority belongs to CYR)

1. First merge `erdos/Challenge/Erdos291.lean` and `erdos/ErdosLab/Erdos291.lean` from ELS
   `c291008b20018ed778500356a81ad56b44fe5519` into `erdos/` on main, and register them in the two index files.
2. FC PR: file `FormalConjectures/ErdosProblems/291.lean`, line 73.
```diff
-@[category research solved, question, AMS 11]
+@[category research solved, question, AMS 11, formal_proof using lean4 at
+  "https://github.com/IamMikeHelsel/ctrl/blob/<SHA>/erdos/ErdosLab/Erdos291.lean#L91"]
 theorem erdos_291.parts.ii :
```
Fallback without merging: `…/blob/c291008b20018ed778500356a81ad56b44fe5519/erdos/ErdosLab/Erdos291.lean#L91` (public backup branch).

The honest framing for the PR body: CYR's formalization (https://github.com/CollinYuanjieRen/awards/blob/5c5716e4c1f4d5ce43b165fe2a49a4ef06747397/submissions/jsp-000247-cyr/README.md,
cited from the erdosproblems.com notes) predates ours. I did not check whether it targets the FC statement verbatim.
FC can carry two links, as `370.lean` does.

Palomar: Steinerberger's argument is "trivially yes" per FC, so this is likely below the floor. JSP: do not file.
JSP-000247 is Open because part (i) is open, and part (ii) alone is partial.

## 5. Verification a human must run (nothing here was built)

```bash
# toolchain
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
source ~/.elan/env
git clone https://github.com/IamMikeHelsel/ctrl && cd ctrl

# 834 (and 261/931) exact FC-import proofs
git checkout 124e2f7787e31cf24f39e1a7b3bf37bf79a93df2
cd erdos && lake exe cache get && lake build Challenge ErdosLab
./scripts/check.sh 834          # build + forbidden tokens + axioms + Expr.const binding
cat > /tmp/Bind834.lean <<'EOF'
import ErdosLab.Erdos834
-- fails unless the ctrl proof has exactly the FC theorem's type
example : type_of% @Erdos834.erdos_834.parts.ii := Challenge.Erdos834.solution
#print axioms Challenge.Erdos834.solution
EOF
lake env lean /tmp/Bind834.lean
cd ..

# 291 (backup snapshot)
git checkout c291008b20018ed778500356a81ad56b44fe5519
cd erdos && lake exe cache get && lake build Challenge.Erdos291 ErdosLab.Erdos291 && ./scripts/check.sh 291
printf 'import ErdosLab.Erdos291\nexample : type_of%% @Erdos291.erdos_291.parts.ii := Challenge.Erdos291.solution\n#print axioms Challenge.Erdos291.solution\n' > /tmp/B291.lean
lake env lean /tmp/B291.lean
cd ..

# 1148 / 367 standalone (root workspace, Mathlib v4.36.0-rc1)
git checkout 124e2f7787e31cf24f39e1a7b3bf37bf79a93df2
lake exe cache get && lake build ControlsLean.Bounty.ErdosWave2
printf 'import ControlsLean.Bounty.ErdosWave2\n#print axioms ControlsLean.Bounty.ErdosWave2.Erdos1148.erdos_1148.variants.weaker\n#print axioms ControlsLean.Bounty.ErdosWave2.Erdos367.erdos_367.variants.k_le_two\n' > /tmp/AxW2.lean
lake env lean /tmp/AxW2.lean

# after porting 1148/367 into erdos/ (section 4.2/4.3), and after bumping the FC pin to the head:
cd erdos && lake update formal_conjectures && lake build Challenge ErdosLab
./scripts/check.sh 1148 && ./scripts/check.sh 367
# + the same `type_of%` binding examples against Erdos1148.erdos_1148.variants.weaker / Erdos367.erdos_367.variants.k_le_two

# FC side, in a formal-conjectures checkout with the attribute edit applied:
lake exe cache get && lake build FormalConjectures.ErdosProblems.«834»   # attribute parses
# JSP self-check, only if a JSP PR is ever filed: TheJustinSunPrize/awards skills/lean-verify/SKILL.md
```
`erdos/scripts/check.py` checks that `solution : Challenge.ErdosN.statement`. It does **not** check that `statement`
equals the FC theorem's type. The `type_of%` example closes that gap and should be added to `check.py`.

## 6. Ordered action list

1. **Fix the docs now.** Delete the 12 Lean-less numbers and the 5 lemma-only numbers from `docs/STATUS_AND_ROADMAP.md:22`,
   `docs/IDEA_PORTFOLIO_AND_SYNERGIES.md:102` and the README count. The honest claim is "6 FC statements formally proved that FC
   already links to others' proofs (261.i, 370, 493, 645, 1179.lower_bound, 1187.ii); 4 FC research-solved statements proved that FC
   does not yet link (834.ii, 1148.weaker, 367.k_le_two, 291.ii, the last with earlier CYR work); 3 statements FC already proves
   inline (931 variant, 951 API, 382 textbook); 1 textbook lemma (311)". The current "29 solved" wording invites a credibility hit.
2. Correct `BOUNTIES.md` and `docs/RESEARCH_FRONTIER_2026-10.md` per the corrections in §0: the plby 291/367 claim, the private-repo claim, and 14 → 4.
3. Bump the `erdos/` FC pin to the head, run §5, and record the outputs.
4. Open the FC PR for 834.ii (§4.1). Then port and open PRs for 1148.weaker (§4.2) and 367.k_le_two (§4.3, preferably inline). The 291.ii PR (§4.4) is optional.
5. Consider a Palomar entry for 834.ii only, and only after checking the registry for an existing entry.
6. JSP: file nothing. Redirect the JSP effort to MATH-05 (Byers–Nash n = 6) or new formalizations.

## 7. Not verified / limits

* No Lean builds anywhere. ctrl's own CI or check-script claims were not re-run.
* JSP PR authors and dates: the GitHub API was refused for TheJustinSunPrize/awards in this session.
  The JSP JSON snapshots are from 2026-10-17, so PRs filed since then are missing.
* Palomar registry contents: the site is blocked. Only Palomar IDs cited inside FC files were seen.
* When the ctrl repo became public: unknown. Only its current visibility was seen.
* Whether CYR's 291 proof and the JSP #455 author's 367 proof target the FC statements verbatim: not checked.
* plby's first-commit date for `Erdos834`: not available from the shallow clone.
