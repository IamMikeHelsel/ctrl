# Erdős Problem 23 — HANDOFF for a fresh agent / new account

**Date:** 2026-07-25
**Repository:** `E:\Projects\ErdosProblems`
**Working folder for this campaign:** `E:\Projects\ErdosProblems\problems\23\`
**Read this file FIRST. Everything you need to resume is here or linked from here.**

---

## 0. Thirty-second orientation

Erdős #23 (Erdős–Faudree–Pach–Spencer 1988, open): for every finite simple **triangle-free**
graph `G` on `N` vertices,

```
bip(G) = |E(G)| - maxcut(G)  <=  N^2 / 25
```

`bip(G)` is the minimum number of edges whose deletion makes `G` bipartite. Sharp: the balanced
blow-up `C5[n]` on `N = 5n` vertices has `bip = n^2 = N^2/25`. Best proved general bound is
Balogh–Clemen–Lidický (*Combinatorica* 43 (2023) 1059–1079, arXiv:2103.14179), ≈ `0.0409 N^2`.

This repository's owner (Alper Ferudun) has **published** the exact values `a(5n) = n^2` for
`1 ≤ n ≤ 40` (arXiv:2606.28041), where `a(N) = max bip` over triangle-free `N`-vertex graphs.

The campaign was halted 2026-07-17, its results published as two arXiv submissions, and
**restarted 2026-07-25** on the template of OpenAI's published Cycle-Double-Cover prompt.

---

## 1. How to start (exact steps)

1. Read this file.
2. Read `problems/23/round1/CLAUDE_GATE_RESULTS.md` — the verified results ledger. Everything in it
   was proved or verified twice in exact arithmetic by the root agent, not merely by a subagent.
3. Read `problems/23/GOAL_TEXT.txt` and paste it as `/goal` (3607 chars, fits the 4000 limit).
4. Read `problems/23/LOOP_TEXT.txt` and paste it as `/loop` (no interval → dynamic self-pacing).
5. Skim `problems/23/GOAL_LOOP_v10_CDC.md` for why the rules are what they are.
6. Then resume at §6 below ("What to do next").

Do **not** read the 665 KB `problems/23/PROOF_STATE.md` — it is the archived pre-halt ledger
(copy preserved as `PROOF_STATE_v9_ARCHIVE_20260623.md`). The current campaign's ledger is
`round1/CLAUDE_GATE_RESULTS.md`.

---

## 2. The one rule that matters

Imported from the CDC prompt, and it is the formal statement of why the previous campaign died:

> **A route that ends at a lemma equivalent in strength to the conjecture is NOT close to
> completion unless the same round supplies a genuinely new proof of that lemma.**

The previous campaign (Feb–Jul 2026) generated an endless chain of equivalent reformulations —
GERSH charts, shortest-support Hall systems, bank certificates, soft collision flows — each of
which "reduced" the conjecture to something of exactly the same strength. The user's verdict was
*"we fell into an asymptotic-reformulation web"*. The GOAL's **WHAT DOES NOT COUNT** clause
enumerates the disqualifiers; obey it literally.

---

## 3. RESULTS ESTABLISHED IN THE RESTART (all gate-verified by the root agent)

Full detail with proofs, scripts and verification records: `round1/CLAUDE_GATE_RESULTS.md`.

### 3.1 The two theorems that changed the campaign

**R1-C7 — Blow-up identity.** `bip(H[t]) = t^2 · bip(H)` for every graph `H` and integer `t`.
More generally `bip(H[a_1..a_h]) = min over cuts S of H of Σ_{uv monochromatic} a_u a_v`.
*Proof:* splitting class `i` as `a_i / (t−a_i)` makes the monochromatic count **affine in each
`a_i` separately** (a class is independent, so no `a_i^2` term), so the box minimum sits at a
vertex — i.e. some maximum cut is constant on classes. **Verified:** brute force over all graphs on
4,5,6 vertices with `t=2` and 4,5 vertices with `t=3` — 246 pairs, 0 mismatches
(`round1/claude_gate_blowup.py`).

**Consequence 1 — the conjecture is PROVED for every `N ≤ 40`, not just multiples of five.**
`a(5N) ≥ 25 a(N)` (blow up an extremal graph by `t=5`) and the published `a(5m) = m^2` for
`m ≤ 40` give `25 a(N) ≤ a(5N) = N^2`. The published paper states only multiples of five; this
closes the 32 non-multiples below 40 for free.

**Consequence 2 — there is NO asymptotic slack.** If `a(N0) > N0^2/25` then
`a(t·N0) ≥ t^2 a(N0) > (t·N0)^2/25` for every `t`. Hence for every `N0`,
"conjecture for all `N ≥ N0`" **⟺** "conjecture for all `N ≥ 1`"; `c := lim a(N)/N^2 = sup_N a(N)/N^2`;
and the conjecture is exactly `c ≤ 1/25`. Therefore:

* the **effective-threshold route is BLOCKED at its premise** — no `N0` has an easier tail;
* every asymptotic bound upgrades verbatim to every finite `N` (so BCL holds at `N0 = 1`);
* **computing `a(N)` on any finite range can never contribute to a proof** — only to a disproof.
  GOAL rule (d) turns out to be a theorem, not a convention.

### 3.2 The open region

**R1-C6 — Low-degree reduction (proved).** `bip(G) ≤ bip(G−v) + ⌊d(v)/2⌋` (place `v` on the side
with fewer of its neighbours). Since `N^2/25 − (N−1)^2/25 = (2N−1)/25`, any vertex with
`d(v) ≤ (4N−2)/25` closes the induction. Hence **a minimal counterexample has
`δ(G) > (4N−2)/25 ≈ 0.16 N`.**

**High-degree closure.** Häggkvist: triangle-free with `δ > 3N/8` ⟹ `G → C5`; and `G → C5` ⟹
`bip(G) ≤ min_i |V_i||V_{i+1}| ≤ N^2/25` by AM–GM twice (proof in the ledger). *(⚠ The exact
hypothesis of the Häggkvist statement is on the Round-2 adversary's list to re-check against the
source — treat it as provisional until that lands.)*

> **THE ENTIRE REMAINING PROBLEM LIVES IN THE BAND `0.16 N < δ(G) ≤ 0.375 N`**, with edge density
> strictly inside the Balogh–Clemen–Lidický window. This is the target.

### 3.3 Exact ground truth (root-agent censuses, two independent implementations each)

`a(N)` for `N = 4..14`: **0, 1, 1, 1, 2, 2, 4, 4, 5, 6, 7**, and `a(15) = 9` (independently
confirming the published value at `n=3`). The `N=14` value comes from the complete census of all
**445,781,050** connected triangle-free graphs on 14 vertices. Engines:
`round1/claude_exact_bip.cpp` (geng → exhaustive Gray-code maxcut), cross-checked in Python.

Restricting to connected graphs is sound: `bip` is additive over components and `Σ N_i^2 ≤ (Σ N_i)^2`.

### 3.4 Obstructions — do not re-propose these unchanged

| # | Obstruction | Evidence |
|---|---|---|
| R1-C1 | **Naive one-vertex induction is false.** On `C5[n]` the drop is exactly `n` against a budget of `(10n−1)/25` — fails for every `n`, asymptotically by 5/2. | exhaustive, `claude_verify_a12.py` |
| R1-C2 | **Extremal graphs are not blow-ups.** `a(12) = 5`, attained by exactly two graphs (`K?ABBBwerwBw`, `K?BD@g]Qvo^?`); the best C5 blow-up on 12 vertices gives 4. Kills any *exact* Motzkin–Straus-style reduction. | full 1,144,061-graph census, twice |
| R1-C4 | **The elementary C5-homomorphism mechanism misses the extremal graphs.** Both `N=12` extremals and the `N=14` extremal are not C5-colourable; two have `χ = 4`. | own homomorphism search |
| R1-C5 | **Circulants are extremal only at multiples of five.** All 927 triangle-free circulants on `Z_n`, `n ≤ 24`: zero violations; the bound is attained exactly at `n = 5,10,15,20`, always by the C5 blow-up; at every non-multiple the best circulant falls strictly short. | `claude_circulant_sweep.cpp` |
| — | **Extremal graphs are not nested across orders.** No one-vertex extension of an `N=12` extremal reaches `a(13) = 6`. | beam search |
| — | Local move classes with switching sets of size `< 0.34 N` cannot certify `N^2/25`; spectral eigenvalue certificates cap at `0.0429 N^2`. | Round-1 families F2/F6/F8 — **still awaiting root-agent gate** |
| — | **R52/R53 "soft pivot" (inherited) is BLOCKED**: its terminal lemma `canonicalSoftCollisionFeasibleTuple_exists` has strength ≥ the conjecture. | rule (a) |

### 3.5 Corrections I had to make (record them; do not repeat the errors)

1. I first observed `a(N) = floor(N^2/25)` for `4 ≤ N ≤ 14` except `N = 9`, called the bound
   "integrally tight", and targeted the counterexample hunt at the orders `N ≡ ±1 (mod 25)` where
   `frac(N^2/25) = 0.04` (i.e. `N = 24, 26, 49, …`). **Two things were wrong:** (a) R1-C7 proves
   all `N ≤ 40` outright, so `N = 24, 26` were already-settled ground; (b) two independent search
   engines both stop one below the floor at `N = 16` and `N = 17`, so the candidate law is almost
   certainly false from `N = 16` on.
2. The CP-SAT deciders (both a full-cut-system model and a CEGAR variant) are **correct but too
   weak**: they decide `N = 8` instantly and return UNKNOWN at `N = 13`. Do not expect to settle
   `a(16)` this way.

---

## 4. WHERE A COUNTEREXAMPLE COULD STILL LIVE

The user asked, reasonably, whether hunting a counterexample (as with the Jacobian conjecture)
beats chasing a proof. Honest assessment with the current data:

* **Against:** unlike the Jacobian conjecture, here there is a sharp extremal family attaining
  equality *and* a matching upper bound within 2.25 % (`0.04` vs `0.0409`). Everything computed so
  far — 445 M graphs at `N = 14`, 927 circulants to `n = 24`, 573 reduced patterns to 15 vertices,
  thousands of structured and Cayley graphs — sits at or below `1/25`, with `1/25` attained **only**
  by C5 blow-ups.
* **For:** the region `N > 40` with `5 ∤ N` is genuinely unverified, and by R1-C7 a violation at
  *any single* order refutes the conjecture outright.
* **Live targets**, by remaining slack `frac(N^2/25) = 0.04`:
  `N = 49, 51, 74, 76, 99, 101, 124, 126, 149, 151, 174, 176, 199` — and anything `> 200`.
* **The right search space** is not raw graphs but **weighted patterns**: by R1-C7 the conjecture
  is exactly `max_x ψ(H,x) ≤ 1/25` for every triangle-free `H`, where
  `ψ(H,x) = min over cuts S of Σ_{uv monochromatic} x_u x_v` on the simplex. Blowing up a rational
  maximiser realises the ratio. Raw-graph annealing is useless at scale (at `N = 30` it reaches 28
  against a true 36).

---

## 5. WHAT IS STILL RUNNING / UNHARVESTED AT HANDOFF TIME

These produced files but **have not passed the root-agent gate**. Treat every claim in them as a
CLAIM until you re-verify it yourself.

**All three workflows terminated on the account's session quota** (resets 12:20 Europe/Istanbul).
Agents that ran to completion wrote their files; the rest died mid-flight. Exact tally:

| Workflow | Completed / errored | Outputs on disk |
|---|---|---|
| Round 1: 8 proof families + 8 audits + registry | 10 done / 7 quota-failed | families `round1/F1.md`, `f2_local_switching.md`, `f3.md`, `f4.md`, `f5.md`, `f6_local_search.md`, `f7_blowup_lagrangian.md`, `f8.md`, `f8_top_table.md`; audits only for f1, f2, f5, f6 (`round1/audit_*.md`). **Audits for f3, f4, f7, f8 and the registry agent never ran.** |
| Disproof hunt: 6 construction families + 6 verifiers | 3 done / 6 quota-failed | `round1/h2_perturbed_blowups.md`, `h3_ramsey_critical.md`, `h5.md`, `h6.md`. **h1 (non-cyclic Cayley) and h4 (exact decision) never ran; NO verifier ran — every hunt claim is unverified.** |
| Round 2: 6 families on the degree band + audits | 0 done / 6 quota-failed | only partial scratch in `round2/`: `g1_graphs.py`, `g3_lib.py`, `g4_lib.py`, `g6_b1_blowup.cpp/.exe`, `g6_b4_reduce.cpp/.exe`, `g6_b4_threshold.py`, `all_h*.g6`, `b1_h8.out`, `b4_n12.out`, plus two downloaded papers (`andrasfai_bipartification_0907.3928.pdf`, `brandt_thomasse_vega11.pdf`). **No Round-2 family produced a report. Round 2 must be re-run from scratch on the new account** — the script is reproducible from §6 item 3 below and the workflow definition is at
`.claude/projects/…/workflows/scripts/erdos23-round2-degree-band-wf_55b1f4de-ae8.js`. |

Beam search finished its run: lower bounds `a(16) ≥ 9`, `a(17) ≥ 10`, `a(18) ≥ 12`, `a(19) ≥ 13`
(against floors 10, 11, 12, 14). Log: `round1/beam2.out`.

**Notable unverified claims worth gating first** (highest value):

* `bip(Higman–Sims) = 350 = 0.035·N^2` exactly, and `bip(Hoffman–Singleton) = 50`,
  `bip(Gewirtz) = 84`, `bip(Clebsch) = 8` (from F5/F8).
* `max_x ψ(H,x) = 1/25` for **all 573 reduced patterns on 5–15 vertices**, attained only by C5
  blow-ups (F8). If true this is the strongest single piece of evidence for the conjecture, and it
  says any counterexample admits **no homomorphism into any triangle-free graph on ≤ 15 vertices**.
  **Partially gated 2026-07-25 (R1-C8):** my own ψ engine on ten named patterns found nothing above
  `1/25`, with C5 the unique maximiser and Wagner `C8(1,4)` the closest rival at
  `15341/396900 = 0.038652`; engine validated by `ψ(C5,unif) = 1/25`, `ψ(C7,unif) = 1/49`,
  `ψ(K_{m,m}) = 0` exactly. **But this is one-sided** — hill-climbing gives only lower bounds, so
  the ceiling is *not refuted* and *not confirmed*. §3g of the ledger records the exact form a
  rigorous certificate must take and proves that the two obvious averaging certificates fail (a
  uniform distribution over all cuts gives only `1/8`; the five rotation cuts of `C5` give `1/20`,
  failing even on `C5` where the truth is `1/25`), because the inner maximum sits at a degenerate
  point where a different cut is active. **A valid certificate needs an `x`-dependent multiplier:
  an SDP/Lasserre relaxation with an exactly verified rational dual, or certified global
  optimisation over the support lattice.** That is the concrete open technical task.
* The density window: the conjecture survives only for `0.2486 < density < 0.3197` at every order
  (F1/F6, from BCL upgraded by R1-C7's no-slack theorem).
* `bip` is NP-hard on triangle-free graphs via 3-subdivision (`bip(G^(3)) = bip(G)`), hence no
  polynomial convex relaxation can be exact unless P = NP (F5).
* The sharp star lemma `Σ_{a ∈ N_B(v)} max(2 − σ(a), 0) ≤ σ(v)` at maximum cuts (F2), strictly
  stronger than the star inequality in the accepted base.

---

## 6. WHAT TO DO NEXT (ordered)

1. **Gate the unharvested claims in §5.** You are the verification gate; nothing enters the ledger
   without your own re-implementation or exact replay. Start with the `ψ`-pattern claim and the
   Higman–Sims value, since they are the load-bearing ones.
2. ~~Re-check the Häggkvist hypothesis against the source.~~ **DONE 2026-07-25 — CONFIRMED.**
   Verified against arXiv:2408.05547 (*Triangle-free Graphs with Large Minimum Common Degree*, 2024),
   which states it as: *every triangle-free graph with minimum degree greater than `⌊3n/8⌋` is
   homomorphic to a cycle of length 5*, attributed to Häggkvist 1982. The conclusion really is a
   homomorphism to `C5` (not merely 3-colourability), there is no largeness condition on `n`, and
   the hypothesis carries a **floor**, i.e. `δ > ⌊3n/8⌋`, which is very slightly *weaker* than the
   `δ > 3n/8` I had assumed — so the closure covers slightly more graphs, not fewer.
   **The open band is therefore `(4N−2)/25 < δ(G) ≤ ⌊3N/8⌋`, and the Round-2 aim is correct.**
   (Still worth doing: read Häggkvist's original 1982 paper directly rather than a 2024 citation of
   it, and pin down Jin's `10n/29` and the Chen–Jin–Koh `n/3` statements the same way, since
   Round-2 family G1's route depends on the exact form of the latter.)
3. **Attack the band.** The most concrete route found so far: for `δ > N/3` there is a structure
   theorem (Chen–Jin–Koh: homomorphic to an explicit finite family of Andrásfai-type graphs, or
   contains an induced Grötzsch graph). If `max_x ψ(H,x) ≤ 1/25` for each graph in that finite
   list — a *finite, checkable* computation — the conjecture follows for `δ > N/3`, leaving only
   `0.16N < δ ≤ N/3`. Round 2's family G1 was launched on exactly this; harvest it.
4. **Improve the low-degree constant `4/25` upward** (Round 2 family G2). Deleting `N(v)` — which
   is *independent* because `G` is triangle-free — or an independent set, instead of a single
   vertex. Every improvement shrinks the band from below. Note naive `N[v]`-peeling fails on
   `C5[n]` (the survivor's whole budget is consumed).
5. **Extend the pattern search** (`max_x ψ(H,x)`) to maximal triangle-free twin-free graphs on
   16–18 vertices. `geng` has **no** maximal-triangle-free flag (`-f` means 4-cycle-free); a
   triangle-free graph is maximal iff every non-adjacent pair has a common neighbour, so filter or
   write a direct generator.
6. **Keep at least three incompatible routes alive** and run an adversarial audit every round, per
   the LOOP text. Do not let the portfolio collapse onto one attractive reduction.

---

## 7. TOOLING BUILT THIS SESSION (all in `problems/23/round1/`, all validated)

| File | What it does | Validation |
|---|---|---|
| `claude_exact_bip.cpp` | graph6 in → exhaustive Gray-code maxcut → census driver for `a(N)` | reproduces `a(N)`, `N ≤ 14` |
| `claude_collect_extremal.cpp` | collects every graph with `bip ≥ T` from a geng stream | 8 hits at `N=13, T=6` |
| `claude_circulant_sweep.cpp` | all triangle-free circulants on `Z_n`, exact maxcut | 927 graphs, `n ≤ 24` |
| `claude_hunt.cpp` | simulated annealing over triangle-free graphs, exact `bip` objective | hits true `a(13)=6` in 1235 iters |
| `claude_beam.cpp` / `claude_beam2.cpp` | order-by-order beam search; every one-vertex extension (new neighbourhood must be an independent set), exact `bip`; v2 adds hashed dedup, wide beams, C5-blow-up injection at every order | reproduces `a(14)=7`, `a(15)=9` |
| `claude_exact_decide.py` | CP-SAT + lazy CEGAR cut constraints: decides `a(N) ≥ t` | correct but too weak past `N=12` |
| `claude_decide_full.py` | CP-SAT with all `2^(N−1)` cut constraints + degree symmetry breaking | correct at `N=8`, UNKNOWN at `N=13` |
| `claude_verify_a12.py`, `claude_identify_n12.py`, `claude_extremal_structure.py`, `claude_gate_blowup.py` | independent Python verifiers (own graph6 decoders, own maxcut) used as the second implementation on every claim | — |

Compiler: `C:\msys64\mingw64\bin\clang++.exe -O3 -march=native -std=c++17`.
nauty geng: `E:\Projects\ErdosProblems\tools\nauty2_8_9\geng.exe` (set `GENG` env var where needed).
Parallel census driver pattern: `run_lane14.cmd` (residue splitting `geng ... r/mod | exe`).

---

## 8. STANDING PROJECT RULES (carry these over)

* **Never** add a `Co-Authored-By: … <noreply@anthropic.com>` (or any Anthropic/Claude) trailer to
  a git commit. Commit as the user alone — a repo they contribute to gates on CLA coverage.
* PROGRESS protocol is mandatory: one `►`/`✔` line per major action in `PROGRESS.md`, ≤ 200 chars,
  with an independently verifiable RESULT. The words *progress, promising, almost, good news* are
  banned inside RESULT; `RESULT: nothing` is required when a step produced nothing.
* Exact integer or rational arithmetic on every acceptance path. Never floating point for a claim.
* Compute cap 64 threads. No WSL — native `clang++` with multithreading.
* The published `N ≤ 200` paper (arXiv:2606.28041) and the two 2026-07-17 submissions
  (`submit/7816436`, `submit/7837759`) are **untouchable**; see
  `problems/23/ERDOS23_LEDGER_CLOSED_20260717.md`.

---

## 9. Pointers

| What | Where |
|---|---|
| **Verified results ledger (read this)** | `problems/23/round1/CLAUDE_GATE_RESULTS.md` |
| GOAL text to paste as `/goal` | `problems/23/GOAL_TEXT.txt` |
| LOOP text to paste as `/loop` | `problems/23/LOOP_TEXT.txt` |
| Why the rules are what they are | `problems/23/GOAL_LOOP_v10_CDC.md` |
| Pre-halt technical restart record | `problems/23/ERDOS23_FINAL_HANDOFF_20260712.md` |
| Publication + ledger closure record | `problems/23/ERDOS23_LEDGER_CLOSED_20260717.md` |
| Archived pre-halt ledger (665 KB, historical) | `problems/23/PROOF_STATE_v9_ARCHIVE_20260623.md` |
| Dead routes with their exact falsifiers | `ERDOS23_FINAL_HANDOFF_20260712.md` §8 |
| Round-1 / disproof / Round-2 raw agent outputs | `problems/23/round1/*.md`, `problems/23/round2/*` |
| Append-only action log | `PROGRESS.md` (repo root) |
| Source of the prompt template | `https://cdn.openai.com/pdf/04d1d1e4-bc75-476a-97cf-49055cd98d31/cdc_prompt.pdf` (WebFetch cannot read it; extract with PyMuPDF) |

---

## 10. Honest status line

The conjecture is **open**. This session did not prove it and did not refute it. What it produced
is: the conjecture settled for every `N ≤ 40` (previously only multiples of five), a theorem that
threshold and finite-range arguments are structurally incapable of proving it, an explicit open
degree band, five exactly-verified obstructions that kill five natural routes, and a validated
toolchain. That is real ground gained, and it is all in
`problems/23/round1/CLAUDE_GATE_RESULTS.md`.
