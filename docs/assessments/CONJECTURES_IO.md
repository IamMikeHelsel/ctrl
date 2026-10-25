# conjectures.io — assessment

Researched 2026-10-17 from the live site, its public JSON API, and the `conjectures-io` GitHub org.
Prices and bounty numbers are snapshots at about 17:50 UTC that day.

## TL;DR

- conjectures.io is **Bittensor Subnet 66 (SN66)**. It pays a bounty for a Lean 4 proof (or disproof)
  of an exact, pinned formal statement. Statements come mostly from Google DeepMind's
  `formal-conjectures` repo, plus 16 "package-authored research targets" that the operators wrote
  themselves.
- **244 open targets**: 203 Erdős problems, 32 Wikipedia-named conjectures, 8 research targets, and
  the Riemann Hypothesis. Each currently shows **about $3,914** (Erdős/Wikipedia/RH) or
  **about $3,140** (research targets). Bounties are paid in **SN66 alpha**, not TAO. The whole pool
  is about **$39.7k**, so the displayed bounties cannot all be paid at once (see Payout).
- Every target is a genuinely open research problem. There are **no trivial, easy, or medium
  items**. The only things that have actually paid out are the operator-written research targets
  (special cases of lonely runner, graceful trees, Wilf's conjecture, and minimal graphs) plus a few
  Erdős and Green problems.
- Cost per attempt is **1 credit = 0.25 TAO, about $68**. Checking a file is free. Every open
  problem requires the **original AI chat logs** that produced the proof, and once accepted, those
  logs are **licensed to conjectures.io for resale (including for AI training)**.
- **No KYC** is mentioned anywhere: no identity checks, no jurisdiction exclusions, no tax forms.
  You need an account, a Bittensor wallet for payout, and you accept that your display name or
  coldkey is published with every result.
- There is a **public, unauthenticated JSON API** (`https://conjectures.io/v1/...`) and public
  GitHub repos with every task bundle.

## How it works

### Flow

1. Create an account (password, Google, email link, or a Talisman / TAO.com wallet).
2. Pick a target. Each problem has two tasks, `formalized` (prove `P`) and `counterexample`
   (prove `¬P`). Both compete for **one** reward per `reward_target_id`, and the first accepted
   answer wins.
3. Write `Main.lean`. Checking it on the website, or with `conjectures check` / `conjectures verify`
   from the CLI, is free.
4. Buy credits with TAO from a linked wallet, or with other crypto through TMC Pay. Invitations can
   also cover attempts.
5. Upload the chat-log package, then submit. Submitting spends one credit.
6. Verification runs, then human review, then payout in alpha to the payout coldkey you set.

### Submission format

- One UTF-8 file, `Main.lean`, containing declarations only. It is placed between a trusted header
  (imports plus `namespace Bounty`) and a trusted footer. The target always looks like this:

  ```lean
  theorem target : fcTypeOfName% "Math30Catalog.source16" := by
    ...
  -- counterexample mode:
  theorem target : ¬ (fcTypeOfName% "Math30Catalog.source16") := by
    ...
  ```

- **Refused by the static scanner:** `import`, `sorry`/`admit`/`sorryAx`, `axiom`/`constant`,
  `native_decide`, `set_option` (so `maxHeartbeats` cannot be raised), `run_cmd`/`run_tac`,
  `instance`, attributes, `macro`/`syntax`/`notation`, `unsafe`/`extern`, interpolated strings,
  and any reference to the source theorem.
- **Permitted axioms:** `propext`, `Quot.sound`, `Classical.choice`.
- **Limits:** the task's `timeout_seconds` (3600 on the tasks inspected) and
  `max_submission_bytes` of 30 MiB. Accepted proofs have been about 1 MB (the Wilf research-target
  proof is 1,052,061 bytes).
- **Bundle:** the `conjectures-submission/v1` zip format, sealed by `conjectures build`.

### Lean version and environment (pinned; `GET /v1/catalog/meta`)

| Component | Pin |
| --- | --- |
| Lean | `leanprover/lean4:v4.35.0-rc2` (commit `11acb17e…`) |
| Mathlib | `065356127b1dc0016f66b7283ce0ce2c4055aa55` |
| formal-conjectures | `4b69a7dca3e731dd1f28cb523b9ebd2ea32527f4` |
| Comparator | `leanprover/comparator` `32bd61da…` |
| lean4export | `6cea9778…` |
| Sandbox | Landrun + seccomp (Nanoda disabled) |

The formal-conjectures commit is **not in upstream** `google-deepmind/formal-conjectures`. It is a
derived source: upstream plus the patch at `conjectures-tasks/tiers/tier-1/formal-conjectures-audit-fixes.patch`,
which adds `FormalConjectures/ResearchTargets/Math15.lean` and `Math30.lean` and the `Math15/` and
`Math30/` support libraries. To reproduce the environment, apply that patch, or use
`conjectures-validator/scripts/bootstrap.sh`.

Pins rotate weekly with submissions drained first. A proof is checked against the version it was
written for.

### Verification

Verification runs in an isolated container (no network, Landlock, seccomp, UID 10001). The stages
are: static policy scan, then build the trusted challenge, then **Comparator** (which checks
statement identity and axiom closure and replays the proof through the kernel), then the Lean
kernel. A plain `lake build` is never treated as acceptance. A Lean-valid proof is then held for
**human review**, which can reject it only for a published reason code:

`ADMITTED_DEPENDENCY`, `TRIVIALISED_STATEMENT`, `FORBIDDEN_IMPORT`, `UNPERMITTED_AXIOM`,
`NOT_NOVEL`, `PRIOR_EXTERNAL_FORMALIZATION`, `DUPLICATE_OF_EARLIER_SUBMISSION`,
`MISATTRIBUTED_WORK`, `ABUSE`, and, from the chat-log terms, `CHAT_LOGS_NOT_ACCEPTED`.

`NOT_NOVEL` is strict (review policy v4). If a complete, established public proof of the same
problem predates acceptance, the bounty is lost, even if that proof was never formalized and even
if your work is an independent rediscovery.

If a formal statement doesn't match the intended conjecture, a proof that exploits the mismatch
earns a **`FORMALIZATION_DEFECT_AWARD`** instead: the smaller of **$750** (in alpha) and the locked
bounty.

### Payout

- Paid in **SN66 alpha** to a Bittensor coldkey (set in account settings via Talisman or TAO.com).
  Dollar figures are estimates. Alpha is currently about $0.70 (pool 56,666.77 α ≈ $39,658). TAO is
  about $271.
- **Pricing rule** (`linear-age-v3-chat-logs`): a new target opens at 2.5% of the *available
  treasury* and rises linearly to 12.5% over 15 days. The amount is locked when you submit (but
  locking does not reserve the target). That is why every target shows about $3.9k while the whole
  pool is $39.7k. Each payout shrinks the pool for everyone else.
- **History:** 36 rewards paid, totalling $114,289 (163,366 α). 47 proofs Lean-verified, 9 rejected
  by Lean, 56 submissions in all.
- **Chat-log bonus:** proofs submitted before chat-log intake opened can earn an extra $500
  (Erdős) or $250 (other) for accepted logs.

### Eligibility, KYC, and other obligations

- **No KYC, no jurisdiction or sanctions clause, no age clause, no tax paperwork** in the Terms of
  Service, Submission Terms v11 (effective 2026-10-14), Privacy, or FAQ. The operator never holds
  keys. Payouts go to whatever coldkey you name.
- **Public attribution:** every result names the solver (display name, or the signing coldkey if
  no name is set). Approved proofs are published in full at `GET /v1/results/{id}`. Failed attempts
  can be linked back to you by timing.
- **Chat logs (required for every open problem):** you must upload the original agent transcripts
  (`conjectures-chat-log/v2` zip: `events.jsonl`, `episodes.jsonl`, manifest, and artifacts). Once
  accepted, you grant conjectures.io a **permanent, worldwide, non-exclusive right to use, copy,
  sell and license them, including for AI training**. You also promise that your AI provider's
  terms allow this. **This needs a policy check before we submit anything produced with
  Claude/Cursor transcripts.**
- **Credits** are non-refundable and non-transferable. They are refunded only if the attempt could
  not run because of a problem on the operator's side.
- **Discrepancy:** the validator README says 0.5 TAO per attempt, but the live API (`credit_price_rao`
  = 250,000,000) and the how-it-works page say 0.25 TAO. The API figure is authoritative.

## API and repositories

All endpoints are unauthenticated GETs unless noted.

| Endpoint | What it returns |
| --- | --- |
| `GET /v1/catalog/meta` | Pins, credit price, treasury and bounty policy, open-target count |
| `GET /v1/catalog/conjectures?limit=100&offset=N` | Paginated catalog (274 entries): slug, statement (pretty-printed Lean type), summary, AMS subjects, task IDs, bounty, attempts |
| `GET /v1/catalog/conjectures/{slug}` | Full detail, including `challenge_lean` and the `machine_contract` (permitted axioms, forbidden deps, timeout, byte limits) |
| `GET /v1/tasks`, `GET /v1/tasks/{task_id}` | 488 task IDs with bundle SHA-256s |
| `GET /v1/results/{id}` | Published solution source for approved results |
| `GET /v1/system/status` | Validator status |
| `POST /v1/submissions`, `/v1/submissions/preflight`, `/v1/me/...`, `/v1/auth/...` | Submission and account endpoints (authenticated, used by the CLI) |

Repositories (all under `github.com/conjectures-io`):

- `conjectures-validator`: verifier, task generator, and sandbox (Python, Lean, Docker).
- `conjectures-tasks`: immutable task bundles (`versions/<task_id>/Challenge.lean`, `manifest.json`,
  …), `allowlist.json`, `POOL.md`, and the tier-1 audit records. The audit records include holds,
  external-solution retirements, and the patch containing the research-target Lean source.
- `conjectures-miner`: the `conjectures` CLI (`tasks sync/list/show/challenge`, `build`, `verify`,
  `check`, `pay`, `logs upload`, `submit`).
- `formal-conjectures`: a fork of DeepMind's repo. The pinned commit is not pushed there; use the
  patch instead.
- Also: optimisation-competition repos (DEFLATE, float kernels). These are a separate
  "faster code plus Lean equivalence proof" track, out of scope here.

## What has actually been solved (calibration)

Paid or approved research targets were all special cases written by the operators:

- Lonely runner: two-entry tight classification, four-speed spectrum, six-speed denominator bound.
- Graceful trees: two degree-pattern families.
- Wilf's inequality for c ≤ 4m.
- Polynomial minimal graphs: affine for degree ≤ 4, and affine in dimension 8.

Solved Erdős and Green entries: Erdős 14 (i, ii), 18b, 96, 108, 196, 272, 354, 416, 579, 653, 726,
859, 944, 1057, 1062-ii; Green 15, 24, 39, 40, 47, 51.

Most solves come from a handful of handles (JenW1N, Elias, gus, Jordan), apparently running heavy
AI-agent pipelines, often within a day or two of a target opening.

**Effectively claimed right now:** research targets 25 (Pólya λ₃), 26 (Pólya λ₄), and 30
(minimal-graph degree bound) each have a Lean-verified submission dated 14–15 Oct that is awaiting
review. They still show as OPEN in the catalog but are first-come-taken unless review rejects them.

## Difficulty assessment

Every entry is labelled **open-research** because that's what it is: an unsolved conjecture,
admitted only after an audit confirming it is still open. The useful distinctions are *shape*
(finite certificate vs. infinitary statement) and *fit*, not "easy vs. hard".

- Famous problems (RH, Goldbach, twin primes, Collatz/Erdős 1135, odd perfect numbers, Hadamard,
  inscribed square, inverse Galois, Lehmer, and so on) are realistically unattainable.
- Erdős entries are mostly asymptotic-density or Sidon-type number theory and combinatorics. Their
  Lean statements often hide an `answer(sorry)` compiled as `True ↔ P`, so the formalized task
  proves `P` and the counterexample task proves `¬P`.
- The operator-written research targets are the only family with a track record of being
  attackable. Five remain unclaimed: 16, 18, 20, 21, 27.

## Five most promising entries for our skill set

Ranked by fit with controls, linear algebra, estimation, applied math, CV geometry, and
elementary-to-medium Mathlib. None of them is easy.

1. **Research target 16: complex 4×4 matrix multiplication with ≤ 47 products** (`math30catalog-source16`, about $3,140).
   `HasBilinearAlgorithm ℂ 4 47`: find linear forms `left t`, `right t` and matrices `output t`
   with `A * B = Σ_{t<47} (left t A · right t B) • output t`.
   - **Fit:** this is pure numerical linear algebra and optimization: alternating least squares or
     Levenberg–Marquardt on the CP decomposition, flip-graph search, then rationalizing into
     ℚ(i) or ℚ[t]/(f). Once a decomposition is found, the Lean side is a finite polynomial identity
     (16 entries, bilinear in 32 variables), which is medium Mathlib work. `native_decide` and
     `set_option` are banned, so the identity needs `ext` / `simp` / `ring` / `linear_combination`
     within default heartbeats, possibly split into lemmas.
   - **Status:** best known rank is 48 (AlphaEvolve over ℂ, rationalized by Dumas–Pernet–Sedoglavic).
     Rank 47 is known only over 𝔽₂. This is also an Epoch FrontierMath open problem, so large labs
     are searching. **Difficulty:** open-research, though the search is the hard part and the
     verification is medium.
2. **Research target 27: Pólya inequality |Ω|·λ_k ≥ 4πk on convex planar domains** (`math30catalog-source27`, about $3,140), plus an audit of its formalization.
   - **Fit:** variational and spectral applied math. The definitions (H₀¹ as the closure of a
     smooth gradient graph in L²×L², Courant–Fischer over finite-dimensional trial spaces) are
     readable Mathlib.
   - **Angle:** targets 25 and 26 (the much harder general λ₃ and λ₄ cases) were Lean-verified
     within days of opening. That suggests either a strong pipeline or a defect in the shared
     `PlanarLipschitzDomain` / `dirichletEigenvalue` setup. If a defect exists and also applies to
     27, it is worth the $750 defect award, or the full bounty if the reviewers judge it fair.
   - **Difficulty:** open-research mathematically. Defect hunting is medium.
3. **Research target 21: bs(f) ≤ C·s(f)³** (`math30catalog-source21`, about $3,140), with **target 20** (s ≤ C·deg^(2−ε)) as a sibling.
   - **Fit:** Huang's sensitivity proof is a signed-adjacency-matrix eigenvalue interlacing
     argument, which is linear algebra and spectral methods. The Boolean-function setup lives in
     the patch's `Math30/MatrixBoolean.lean`, with finite types only.
   - **Status:** the best known bound is quartic. **Difficulty:** open-research (a real TCS
     breakthrough would be needed).
4. **Euclidean distance-geometry Erdős cluster: 1082-i, 982, 98, 89, 100, 213** (about $3,914 each).
   - **Statements:** for example, 1082-i: non-collinear n-point sets determine at least ⌊n/2⌋
     distinct distances; 982: a convex polygon has a vertex with at least ⌊n/2⌋ distinct distances.
   - **Fit:** planar point configurations and `EuclideanSpace ℝ (Fin 2)`, close to CV geometry.
     There are compact finitary statements, so the counterexample mode is a possible avenue for
     small cases.
   - **Difficulty:** open-research. Check `NOT_NOVEL` against the erdosproblems.com threads first.
5. **Hadamard conjecture** (`Hadamard`, about $3,914, linear algebra).
   - **Fit:** matrix construction (Paley, Williamson, Sylvester), which is in our wheelhouse.
   - **Catch:** the formal statement is for **all** n = 4k. The smallest open order is 668, and
     finding it would not prove the conjecture. **Difficulty:** open-research. Included for fit
     only; realistic payout is near zero.

**Cheaper side angle:** formalization-defect hunting across the catalog, especially the
package-authored Math15/Math30 definitions and any `answer(sorry)` / ℕ-truncation slips like the
held `Erdos564` (an untyped constant `c` elaborated as `Nat`). This matches elementary-to-medium
Mathlib skills. The payout is capped at min($750, bounty) and still requires a credit, chat logs,
and review.

## Problem table (244 open targets)

Difficulty is `open-research` for every row (see above). Bounties are dynamic estimates in USD,
paid in alpha. "Area" comes from the AMS subject codes in the catalog, or a manual label for the
research targets. Summaries are trimmed from the catalog's `summary` field. Exact Lean statements
are available at `GET /v1/catalog/conjectures/{slug}`.

| Problem | Statement summary | Prize | Area | Difficulty | Notes |
| --- | --- | --- | --- | --- | --- |
| All positive-index Dirichlet Polya inequalities on convex planar domains | Pólya |Ω|·λ_k ≥ 4πk for all k≥1 on convex planar Lipschitz domains. | $3,140 | Spectral theory / PDE | open-research | Check whether 25/26 proofs exploit a defect that also hits 27 |
| Complex 3x3 border rank at least 18 | Border rank (Zariski closure) of 3x3 matmul tensor over ℂ is ≥18 (known ≥17, Conner–Harper–Landsberg). | $3,140 | Alg. geometry / tensors | open-research |  |
| Complex 4x4 exact bilinear multiplication with at most 47 products | Exists exact bilinear algorithm for 4x4 complex matrix mult. with ≤47 products (best known: 48). Finite certificate. | $3,140 | Linear algebra / tensors | open-research | Computational search; Lean check is a finite identity |
| For every dimension n>=8 there is a degree bound uniform over all scalar real polynomial minimal graphs | For n≥8, uniform degree bound on polynomial solutions of the minimal-graph equation in n variables. | $3,140 | Minimal surfaces / PDE | open-research (claimed) | Lean-verified 15 Oct (JenW1N), in review — effectively claimed |
| Fourth planar Dirichlet Polya inequality, area times lambda4 at least 16pi | Pólya: |Ω|·λ₄(Ω) ≥ 16π for bounded planar Lipschitz domains. | $3,140 | Spectral theory / PDE | open-research (claimed) | Lean-verified 14 Oct (Jordan), in review — effectively claimed |
| Third planar Dirichlet Polya inequality, area times lambda3 at least 12pi | Pólya: |Ω|·λ₃(Ω) ≥ 12π for bounded planar Lipschitz domains (Courant–Fischer on H₀¹ graph). | $3,140 | Spectral theory / PDE | open-research (claimed) | Lean-verified 14 Oct (JenW1N), in review — effectively claimed |
| Uniform cubic ordinary-sensitivity upper bound for block sensitivity | ∃C: bs(f) ≤ C·s(f)^3 for all Boolean f (Huang gives quartic). | $3,140 | Boolean functions / TCS | open-research |  |
| Uniform subquadratic sensitivity-versus-exact-real-degree upper bound | ∃C,ε>0: s(f) ≤ C·deg(f)^(2−ε) for all nonconstant Boolean f (known: quadratic). | $3,140 | Boolean functions / TCS | open-research |  |
| Artin Primitive Roots Conjecture - part i | Artin's Conjecture on Primitive Roots, first half. Let $a$ be an integer that is not a square number and not $−1$. Then the set $S(a)$ of primes $p$ such that $a$ is a… | $3,914 | Number theory | open-research |  |
| Borsuk Conjecture - four | Borsuk's conjecture in dimension $4$, the smallest open case. | $3,914 | Convex/discrete geometry | open-research |  |
| Brocard Conjecture | Brocard's Conjecture For every `n ≥ 2`, between the squares of the `n`-th and `(n+1)`-th primes, there are at least four prime numbers. | $3,914 | Number theory | open-research |  |
| Bunyakovsky | Bunyakovsky conjecture If a polynomial $f$ over integers satisfies both Schinzel and Bunyakovsky conditions, there exist infinitely many natural numbers $m$ such that… | $3,914 | Number theory | open-research |  |
| Carmichael Totient - charmichael Totient | *Carmichael's totient function conjecture*: For every positive natural number $n$, there exists a natural number $m$ with $m ≠ n$, such that $φ(n) = φ(m)$. | $3,914 | Number theory | open-research |  |
| Class Number Problem | There are infinitely many real quadratic fields `ℚ(√d)` with class number one, where `d > 1` is a squarefree integer. | $3,914 | Number theory | open-research |  |
| Dickson | Dickson's conjecture If a finite set of linear integer forms $f_i(n) = a_i n+b_i$ satisfies Schinzel condition, there exist infinitely many natural numbers $m$ such th… | $3,914 | Number theory | open-research |  |
| Fermat - infinite fermat primes | Are there infinitely many Fermat primes? | $3,914 | Number theory | open-research |  |
| Gauss Circle Problem - error is Big O | It is conjectured that the correct bound is $$ \|E(r)\| = O\left(r^{1/2 + o(1)}\right) $$ [Ha59] Hardy, G. H. (1959). _Ramanujan: Twelve Lectures on Subjects Suggested… | $3,914 | Number theory | open-research |  |
| Goldbach Conjecture | Can every even integer greater than 2 be written as the sum of two primes? | $3,914 | Number theory | open-research |  |
| Goormaghtigh | The only Goormaghtigh numbers are $31$ and $8191$. | $3,914 | Number theory | open-research |  |
| Hadamard | There exists a Hadamard matrix for all $n = 4k$. | $3,914 | Linear algebra | open-research |  |
| Hardy Littlewood - first hardy littlewood conjecture | Let $P = (m_1, \dots, m_k)$ be a tuple of distinct positive even integers. Let $\pi_P(n)$ denote the number of primes $p\leq n$ such that $(p, p + m_1, \dots, p + m_k)… | $3,914 | Number theory | open-research |  |
| Hardy Littlewood - second hardy littlewood conjecture | For integers $x, y \geq 2$, $$ \pi(x + y) \leq \pi(x) + \pi(y), $$ where $\pi(z)$ denotes the prime-counting function, giving the number of primes up to and including… | $3,914 | Number theory | open-research |  |
| Idoneal Completeness - idoneal numbers completeness | Idoneal numbers completeness conjecture. | $3,914 | Number theory | open-research |  |
| Inscribed Square | Inscribed square problem Does every Jordan curve admit an inscribed square? | $3,914 | Geometry | open-research |  |
| Inverse Galois | The Inverse Galois Problem: every finite group is isomorphic to the Galois group of a Galois extension of the rationals. | $3,914 | Field theory | open-research |  |
| Irrational - euler Mascheroni Constant | Is the Euler-Mascheroni constant $\gamma$ irrational? | $3,914 | Special functions | open-research |  |
| Kummer Vandiver | Kummer–Vandiver conjecture states that for every prime $p$, the class number of the maximal real subfield of $\mathbb{Q}(\zeta_p)$ is not divisible by $p$. - | $3,914 | Number theory | open-research |  |
| Legendre Conjecture | Does there always exist at least one prime between consecutive perfect squares? | $3,914 | Number theory | open-research |  |
| Lehmer Mahler Measure Problem | Let `M(f)` denote the Mahler measure of `f`. There exists a constant `μ>1` such that for any `f(x)∈ℤ[x], M(f)>1 → M(f)≥μ`. | $3,914 | Number theory | open-research |  |
| Lehmer Totient | Does there exist a composite number $n > 1$ such that Euler’s totient function $\varphi(n)$ divides $n - 1$? | $3,914 | Number theory | open-research |  |
| Lemoine | For all odd integers $n ≥ 7$ there are prime numbers $p,q$ such that $n = p+2q$. | $3,914 | Number theory | open-research |  |
| Mersenne - catalans mersenne conjecture | The first five Catalan-Mersenne numbers $c_0, \ldots, c_4$ are known to be prime. Catalan conjectured that they are prime "up to a certain limit". Are all Catalan-Mers… | $3,914 | Number theory | open-research |  |
| Mersenne - infinitely many mersenne primes | Are there infinitely many Mersenne primes? | $3,914 | Number theory | open-research |  |
| Normality Of Pi - pi normal base ten | $\pi$ is normal in base 10. | $3,914 | Number theory | open-research |  |
| Oppermann | Oppermann's Conjecture: For every integer $x \ge 2$, the following hold: - There exists a prime between $x(x-1)$ and $x^2$. - There exists a prime between $x^2$ and $x… | $3,914 | Number theory | open-research |  |
| Perfect Numbers - odd perfect number conjecture | Odd Perfect Number Conjecture. The Odd Perfect Number Conjecture states that all perfect numbers are even. *Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Perfe… | $3,914 | Number theory | open-research |  |
| Pollocks Conjecture - pollock tetrahedral | Pollock's (tetrahedral numbers) conjecture: every integer is the sum of at most $5$ tetrahedral numbers. | $3,914 | Number theory | open-research |  |
| Primes And Perfect Squares - infinite prime sq add one | Are there infinitely many primes $p$ such that $p - 1$ is a perfect square? In other words: Are there infinitely many primes of the form $n^2 + 1$? | $3,914 | Number theory | open-research |  |
| Regular Primes - regularprime conjecture | Conjecture: The set of regular primes is infinite. | $3,914 | Number theory | open-research |  |
| Twin Primes | Are there infinitely many primes p such that p + 2 is prime? | $3,914 | Number theory | open-research |  |
| Riemann Hypothesis | The Riemann Hypothesis: all non-trivial zeros of the Riemann zeta function have real part $\frac{1}{2}$. That is, if $\zeta(s) = 0$, $s \neq 1$, and $s$ is not a trivi… | $3,914 | Number theory | open-research | Famous; ignore |
| Erdős problem 9 | Is the upper density of the set of odd numbers that cannot be expressed as a prime plus two powers of 2 positive? | $3,914 | Combinatorics, Number theory | open-research |  |
| Erdős problem 10 | Is there some $k$ such that every integer is the sum of a prime and at most $k$ powers of $2$? | $3,914 | Combinatorics, Number theory | open-research |  |
| Erdős problem 11 | Is every odd $n > 1$ the sum of a squarefree number and a power of 2? | $3,914 | Number theory | open-research |  |
| Erdős problem 17 | Erdős Problem 17. Are there infinitely many cluster primes? | $3,914 | Number theory | open-research | 1 attempt(s) logged |
| Erdős problem 23 | Can every triangle-free graph on $5n$ vertices be made bipartite by deleting at most $n^2$ edges? | $3,914 | Combinatorics | open-research |  |
| Erdős problem 25 | Let $n_1 < n_2 < \dots$ be an arbitrary sequence of integers, each with an associated residue class $a_i \pmod{n_i}$. Let $A$ be the set of integers $n$ such that for… | $3,914 | Number theory | open-research |  |
| Erdős problem 28 | If $A ⊆ \mathbb{N}$ is such that $A + A$ contains all but finitely many integers then $\limsup 1_A ∗ 1_A(n) = \infty$. | $3,914 | Number theory | open-research |  |
| Erdős problem 30 | Is it true that, for every $\varepsilon > 0$, $h(N) = \sqrt N + O_{\varepsilon}(N^\varepsilon)$ | $3,914 | Number theory | open-research |  |
| Erdős problem 32 | Does there exist a set $A \subseteq \mathbb{N}$ such that $\|A \cap \{1, \ldots, N\}\| = o((\log N)^2)$ and every sufficiently large integer can be written as $p + a$… | $3,914 | Number theory | open-research |  |
| Erdős problem 39 | Is there an infinite Sidon set $A\subset \mathbb{N}$ such that $\lvert A\cap \{1\ldots,N\}\rvert \gg_\epsilon N^{1/2-\epsilon}$ for all $\varepsilon > 0$? | $3,914 | Number theory | open-research |  |
| Erdős problem 41 | Let $A \subset \mathbb{N}$ be an infinite set such that the triple sums $a+b+c$ are all distinct for $a,b,c \in A$ (aside from the trivial coincidences). Is it true th… | $3,914 | Number theory | open-research |  |
| Erdős problem 44 | Erdős Problem 44: Let N ≥ 1 and `A ⊆ {1,…,N}` be a Sidon set. Is it true that, for any ε > 0, there exist M = M(ε) and `B ⊆ {N+1,…,M}` such that `A ∪ B ⊆ {1,…,M}` is a… | $3,914 | Combinatorics, Number theory | open-research |  |
| Erdős problem 50 | Let $f$ be the asymptotic distribution function of $\varphi(n)/n$, so that for each $c \in [0,1]$, $f(c)$ is the natural density of $\{n : \varphi(n) < cn\}$. Is it tr… | $3,914 | Number theory | open-research |  |
| Erdős problem 51 | Is there an infinite set $A \subset \mathbb{N}$ such that for every $a \in A$, there is an integer n such that $\phi(n)=a$, and yet if $n_a$ is the smallest such integ… | $3,914 | Number theory | open-research |  |
| Erdős problem 52 | Let $A$ be a finite set of integers. Is it true that for every $\epsilon>0$ $\max( \lvert A+A\rvert,\lvert AA\rvert)\gg_\epsilon \lvert A\rvert^{2-\epsilon}?$ | $3,914 | Number theory | open-research |  |
| Erdős problem 61 | The Erdős–Hajnal Conjecture states that there is a constant $c(H) > 0$ for each $H$ such that we can take $f(n) = n^{c(H)}$ in the above formulation. | $3,914 | Combinatorics | open-research |  |
| Erdős problem 66 | Is there and $A \subset \mathbb{N}$ is such that $$\lim_{n\to \infty}\frac{1_A\ast 1_A(n)}{\log n}$$ exists and is $\ne 0$? | $3,914 | Number theory | open-research |  |
| Erdős problem 68 | Is $$\sum_{n=2}^\infty \frac{1}{n!-1}$$ irrational? | $3,914 | Number theory | open-research |  |
| Erdős problem 82 | $F(n) / \log n \to \infty as n \to \infty$ | $3,914 | Combinatorics | open-research |  |
| Erdős problem 85 | Is it true that, for all large $n$, $f(n + 1) \ge f(n)$? | $3,914 | Combinatorics | open-research |  |
| Erdős problem 89 | Erdős [Er46] asked whether every set of $n$ distinct points in $\mathbb{R}^2$ determines $\gg \frac{n}{\sqrt{\log n}}$ many distinct distances. | $3,914 | Convex/discrete geometry | open-research |  |
| Erdős problem 91 | Suppose $A\subset \mathbb{R}^2$ has $\lvert A\rvert=n$ and minimises the number of distinct distances between points in $A$. Prove that for large $n$ there are at leas… | $3,914 | Convex/discrete geometry | open-research |  |
| Erdős problem 98 | Let $h(n)$ be such that any $n$ points in $\mathbb{R}^2$, with no three on a line and no four on a circle, determine at least $h(n)$ distinct distances. Does $h(n)/n\t… | $3,914 | Convex/discrete geometry | open-research |  |
| Erdős problem 99 | For sufficiently large n, is it the case that any set of n points with minimum distance $1$ that minimizes diameter must contain an equilateral triangle of side length 1? | $3,914 | Convex/discrete geometry | open-research |  |
| Erdős problem 100 | Is the diameter of $A$ at least $Cn$ for some constant $C > 0$? | $3,914 | Convex/discrete geometry | open-research |  |
| Erdős problem 107 | Let $f(n)$ be minimal such that any $f(n)$ points in $ℝ^2$, no three on a line, contain $n$ points which form the vertices of a convex $n$-gon. Prove that $f(n) = 2^{n… | $3,914 | Convex/discrete geometry | open-research |  |
| Erdős problem 120 | Let $A \subseteq \mathbb{R}$ be an infinite set. Must there be a set $E \subseteq \mathbb{R}$ of positive measure which does not contain any set of the shape $a * A +… | $3,914 | Combinatorics, Measure theory | open-research |  |
| Erdős problem 124 - ne zero | Let $k \ne 0$ and $3\leq d_1 < d_2 < \cdots < d_r$ be integers of gcd equal to $1$ such that $$\sum_{1 \le i \le r}\frac 1{d_i - 1} \ge 1.$$ Can all sufficiently large… | $3,914 | Number theory | open-research |  |
| Erdős problem 126 - is Little O | Erdős says that $f(n) = o(\frac{n}{\log n})$ has never been proved. | $3,914 | Number theory | open-research |  |
| Erdős problem 128 | Let G be a graph with n vertices such that every induced subgraph on ≥ $n/2$ vertices has more than $n^2/50$ edges. Must G contain a triangle? | $3,914 | Combinatorics | open-research |  |
| Erdős problem 137 - multiple powerful factors | Erdős [Er82c] conjectures that, if $k$ is fixed, then for all $n$ sufficiently large and all positive integers $m$, there must be at least $k$ distinct primes $p$ such… | $3,914 | Number theory | open-research |  |
| Erdős problem 141 - eleven | Are there $11$ consecutive primes in arithmetic progression? | $3,914 | Combinatorics, Number theory | open-research |  |
| Erdős problem 143 - part ii | Or $$ \sum_{x \in A} \frac{1}{x \log x} < \infty, $$ | $3,914 | Number theory | open-research |  |
| Erdős problem 145 | Let $s_1 < s_2 < \cdots$ be the sequence of squarefree numbers. Is it true that, for any $\alpha\geq 0$, $$ \lim_{x\to\infty} \frac{1}{x}\sum_{s_n\leq x}(s_{n+1}-s_n)^… | $3,914 | Number theory | open-research |  |
| Erdős problem 153 | Let $A$ be a finite Sidon set and $A+A=\{s_1<\cdots<s_t\}$. Is it true that $$\frac{1}{t}\sum_{1\leq i<t}(s_{i+1}-s_i)^2 \to \infty$$ as $\lvert A\rvert\to \infty$? | $3,914 | Combinatorics | open-research |  |
| Erdős problem 155 | Is it true that for every $k \geq 1$ we have $$ F(N + k) \leq F(N) + 1 $$ for all sufficiently large $N$? | $3,914 | Combinatorics | open-research |  |
| Erdős problem 156 | Does there exist a maximal Sidon set $A\subset \{1,\ldots,N\}$ of size $O(N^{1/3})$? A question of Erdős, Sárközy, and Sós [ESS94]. | $3,914 | Combinatorics | open-research |  |
| Erdős problem 158 | Let `A` be an infinite `B₂[2]` set. Must `liminf \|A ∩ {1, ..., N}\| * N ^ (- 1 / 2) = 0`? | $3,914 | Combinatorics | open-research |  |
| Erdős problem 168 - part ii | Is the limit $F(N)/N$ as $N \to \infty$ irrational? | $3,914 | Combinatorics, Number theory | open-research |  |
| Erdős problem 200 | Does the longest arithmetic progression of primes in $\{1,\ldots,N\}$ have length $o(\log N)$? | $3,914 | Combinatorics, Number theory | open-research |  |
| Erdős problem 208 - log bound | In [Er79] Erdős says perhaps $s_{n+1} - s_n \ll \log s_n$, but he is 'very doubtful'. [Er79] Erdős, Paul, __Some unconventional problems in number theory__. Math. Mag.… | $3,914 | Number theory | open-research |  |
| Erdős problem 212 | Is there a dense subset of ℝ^2 such that all pairwise distances are rational? | $3,914 | Convex/discrete geometry | open-research |  |
| Erdős problem 213 | Let $n \geq 4$. Are there $n$ points in $\mathbb{R}^2$, no three on a line and no four on a circle, such that all pairwise distances are integers? | $3,914 | Convex/discrete geometry | open-research |  |
| Erdős problem 218 - ge | The set of indices $n$ for which a prime gap is preceded by a larger or equal prime gap has a natural density of $\frac 1 2$. | $3,914 | Number theory | open-research |  |
| Erdős problem 218 - infinite equal prime gap | There are infinitely many indices $n$ such that the prime gap at $n$ is equal to the prime gap at $n+1$. This is equivalent to the existence of infinitely many arithme… | $3,914 | Number theory | open-research |  |
| Erdős problem 218 - le | The set of indices $n$ for which a prime gap is followed by a larger or equal prime gap has a natural density of $\frac 1 2$. | $3,914 | Number theory | open-research |  |
| Erdős problem 233 | A conjecture by Heath-Brown: The sum of squares of the first $N$ gaps between consecutive primes behaves like $N * (log N)^2$. | $3,914 | Number theory | open-research |  |
| Erdős problem 234 | Is it true that for all `c ≥ 0`, the density `f c` of integers for which `(p (n + 1) - p n) / log n < c` exists and is a continuous function of `c`? | $3,914 | Number theory | open-research |  |
| Erdős problem 236 | Let $f(n)$ count the number of solutions to $n=p+2^k$ for prime $p$ and $k\geq 0$. Show that $f(n)=o(\log n)$. | $3,914 | Combinatorics, Number theory | open-research |  |
| Erdős problem 238 | Let `c₁, c₂ > 0`. Is it true that for any sufficiently large `x`, there exists more than `c₁ * log x` many consecutive primes `≤ x` such that the difference between an… | $3,914 | Number theory | open-research |  |
| Erdős problem 241 - generalization | More generally, Bose and Chowla [BoCh62] conjectured that the maximum size of $A\subseteq \{1,\ldots,N\}$ with all $r$-fold sums distinct (aside from the trivial coinc… | $3,914 | Combinatorics | open-research |  |
| Erdős problem 242 - schinzel generalization | Schinzel conjectured (see [Si56]) the generalisation that, for any fixed $a$, if $n$ is sufficiently large in terms of $a$ then there exist distinct integers $1\leq x… | $3,914 | Number theory | open-research |  |
| Erdős problem 243 | Let $a_1 < a_2 < \dots$ be a sequence of integers such that $\lim_{n\to\infty} \frac{a_n}{a_{n-1}^2} = 1$ and $\sum \frac{1}{a_n} \in \mathbb{Q}$. Then, for all suffic… | $3,914 | Sequences/series | open-research |  |
| Erdős problem 244 | Let $C > 1$. Does the set of integers of the form $p + \lfloor C^k \rfloor$, for some prime $p$ and $k\geq 0$, have density $>0$? | $3,914 | Number theory | open-research |  |
| Erdős problem 247 | Let $n_1 < n_2 < \cdots$ be a sequence of integers such that $$ \limsup \frac{n_k}{k} = \infty. $$ Is $$ \sum_{k=1}^{\infty} \frac{1}{2^{n_k}} $$ transcendental? | $3,914 | Number theory | open-research |  |
| Erdős problem 249 | Is $$\sum_{n} \frac{\phi(n)}{2^n}$$ irrational? Here $\phi$ is the Euler totient function. | $3,914 | Number theory | open-research |  |
| Erdős problem 251 | Is $\sum_{n=1}^\infty \frac{p_n}{2^n}$ irrational? Here $p_n$ is the $n$-th prime ($p_1=2, p_2=3, \dots$). | $3,914 | Number theory | open-research |  |
| Erdős problem 257 | Let $A\subseteq\mathbb{N}$ be an infinite set. Is $$ \sum_{n\in A} \frac{1}{2^n - 1} $$ irrational? | $3,914 | Number theory | open-research |  |
| Erdős problem 263 - part i | Is $a_n = 2^{2^n}$ an irrationality sequence in the above sense? | $3,914 | Number theory | open-research |  |
| Erdős problem 264 - part ii | Is $n!$ an example of an irrationality sequence? | $3,914 | Number theory | open-research |  |
| Erdős problem 269 - irrational | Let $P$ be a finite set of primes with $\|P\| \ge 2$ and let $\{a_1 < a_2 < \dots\}$ be the set of positive integers whose prime factors are all in $P$. Is the sum $$… | $3,914 | Number theory | open-research |  |
| Erdős problem 274 - herzog schonheim | Let $G$ be a group, and let $A = \{a_1G_1, \dots, a_kG_k\}$ be a finite system of left cosets of subgroups $G_1, \dots, G_k$ of $G$. Herzog and Schönheim conjectured t… | $3,914 | Group theory | open-research |  |
| Erdős problem 287 | Let $k\geq2$. Is it true that, for any distinct integers $1 < n_1 < \cdots < n_k$ such that $\sum_{i=1}^k \frac{1}{n_i} = 1$, we must have $\max(n_{i+1} - n_i) \geq 3$? | $3,914 | Number theory | open-research |  |
| Erdős problem 291 - part i | Let $n\geq 1$ and define $L_n$ to be the least common multiple of $\{1,\ldots,n\}$ and $a_n$ by $\sum_{1\leq k\leq n}\frac{1}{k}=\frac{a_n}{L_n}$. Is it true that $(a_… | $3,914 | Number theory | open-research |  |
| Erdős problem 291 - shiu heuristic density zero | In particular, there should be infinitely many $n$, but the set of such $n$ should have density zero. Unfortunately this heuristic is difficult to turn into a proof. | $3,914 | Number theory | open-research |  |
| Erdős problem 307 | Are there two finite set of primes $P$ and $Q$ such that $$ 1 = \left( \sum_{p \in P} \frac{1}{p} \right) \left( \sum_{q \in Q} \frac{1}{q} \right) $$ ? Asked by Barbe… | $3,914 | Number theory | open-research |  |
| Erdős problem 313 - primary pseudoperfect are infinite | It is conjectured that the set of primary pseudoperfect numbers is infinite. | $3,914 | Number theory | open-research |  |
| Erdős problem 317 - claim 2 | Is it true that for sufficiently large $n$, for any $\delta_k\in \{-1,0,1\}$, $$\left\lvert \sum_{1\leq k\leq n}\frac{\delta_k}{k}\right\rvert > \frac{1}{[1,\ldots,n]}… | $3,914 | Number theory | open-research |  |
| Erdős problem 323 - k gt 2 | For $k>2$ it is not known if $f_{k,k}(x)=o(x)$. | $3,914 | Number theory | open-research |  |
| Erdős problem 323 - part i | Is it true that $f_{k,k}(x) \gg_\epsilon x^{1-\epsilon}$ for all $\epsilon>0$? This would have significant applications to Waring's problem. Erdős and Graham describe… | $3,914 | Number theory | open-research |  |
| Erdős problem 323 - part ii | Is it true that if $m < k$ then $f_{k,m}(x) \gg x^{m/k}$ for sufficiently large $x$? | $3,914 | Number theory | open-research |  |
| Erdős problem 324 - quintic | Probably $f(x) = x^5$ has the property that the sums $f(a)+f(b)$ with $a < b$ nonnegative integers are distinct. | $3,914 | Number theory | open-research |  |
| Erdős problem 325 | Writing $f_{k, 3}(x)$ for the number of integers $\leq x$ which are the sum of three $k$th powers, is it true that $f_{k, 3}(x) \gg x ^ (3 / k)$? | $3,914 | Number theory | open-research |  |
| Erdős problem 340 | Let $A = \{1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, \ldots\}$ be the greedy Sidon sequence: we begin with $1$ and iteratively include the next smallest integer that pre… | $3,914 | Combinatorics | open-research |  |
| Erdős problem 340 - sub has Pos Density | Erdős and Graham [ErGr80] also asked about the difference set $A - A$ and whether this has positive density. [ErGr80] Erdős, P. and Graham, R., Old and new problems an… | $3,914 | Combinatorics | open-research |  |
| Erdős problem 357 - infinite set density | Suppose $A$ is an infinite set such that all finite sums of consecutive terms of $A$ are distinct. Then it is conjectured that $A$ has density 0. | $3,914 | Number theory | open-research |  |
| Erdős problem 357 - infinite set sum | Suppose $A$ is an infinite set such that all finite sums of consecutive terms of $A$ are distinct. Then it is conjectured that the sum $\sum_k \frac{1}{a_k}$ converges. | $3,914 | Number theory | open-research |  |
| Erdős problem 357 - monotone, part i | Let $h(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 \leq \dotsc \leq a_k \le n$ such that all sums of the shape $\sum_{u \le i \le v} a_i$ are dist… | $3,914 | Number theory | open-research |  |
| Erdős problem 357 - part i | Let $f(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 < \dotsc < a_k \le n$ such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct.… | $3,914 | Number theory | open-research |  |
| Erdős problem 359 - is Good For 1 asymptotic | Suppose monotone sequence $A$ satisfies the following: `A 0 = 1` and for all `j`, `A (j + 1)` is the smallest natural number that cannot be written as a sum of consecu… | $3,914 | Number theory | open-research |  |
| Erdős problem 359 - part i | Let $a_1< a_2 < ⋯ $ be an infinite sequence of integers such that $a_1=1$ and $a_{i+1}$ is the least integer which is not a sum of consecutive earlier $a_j$s. Show tha… | $3,914 | Number theory | open-research |  |
| Erdős problem 359 - part ii | Let $a_1< a_2 < ⋯ $ be an infinite sequence of integers such that $a_1=1$ and $a_{i+1}$ is the least integer which is not a sum of consecutive earlier $a_j$s. Show tha… | $3,914 | Number theory | open-research |  |
| Erdős problem 364 | There is no consecutive triple of powerful numbers. | $3,914 | Number theory | open-research |  |
| Erdős problem 364 - strong | Erdős [Er76d] conjectured a stronger statement: if $n_k$ is the $k$th powerful number, then $n_{k+2} - n_k > n_k^c$ for some constant $c > 0$. [Er76d] Erdős, P., Probl… | $3,914 | Number theory | open-research |  |
| Erdős problem 366 | Are there any $2$-full $n$ such that $n+1$ is $3$-full? | $3,914 | Number theory | open-research |  |
| Erdős problem 373 | Show that the equation `n!=a_1!a_2!···a_k!`, with `n−1 > a_1 ≥ a_2 ≥ ··· ≥ a_k`, has only finitely many solutions. | $3,914 | Number theory | open-research |  |
| Erdős problem 373 - maximal solution | Hickerson conjectured the largest solution the equation `n!=a_1!a_2!···a_k!`, with `n−1 > a_1 ≥ a_2 ≥ ··· ≥ a_k`, is `16!=14!5!2!`. | $3,914 | Number theory | open-research |  |
| Erdős problem 373 - suranyi | Surányi was the first to conjecture that the only non-trivial solution to `a!b!=n!` is `6!7!=10!`. | $3,914 | Number theory | open-research |  |
| Erdős problem 375 | Is `Erdos375Prop` true? | $3,914 | Number theory | open-research |  |
| Erdős problem 376 | Are there infinitely many $n$ such that ${2n\choose n}$ is coprime to $105$? | $3,914 | Number theory | open-research |  |
| Erdős problem 383 | Is it true that for every $k$ there are infinitely many primes $p$ such that the largest prime divisor of $$ \prod_{i = 0}^k (p ^ 2 + i) $$ is $p$? | $3,914 | Number theory | open-research |  |
| Erdős problem 385 - part i | Let $F(n) := \max\{m + p(m) \mid \textrm{$m < n$ composite}\}\}$ where $p(m)$ is the least prime divisor of $m$. Is it true that $F(n)>n$ for all sufficiently large $n$? | $3,914 | Number theory | open-research |  |
| Erdős problem 386 - two | Can $\binom{n}{2}$ be the product of consecutive primes infinitely often? | $3,914 | Number theory | open-research |  |
| Erdős problem 396 | Is it true that for every $k$ there exists $n$ such that $$\prod_{0\leq i\leq k}(n-i) \mid \binom{2n}{n}?$$ | $3,914 | Number theory | open-research |  |
| Erdős problem 398 | Brocard's Problem Are $n = 4, 5, 7$ the only natural numbers for which $n! + 1 = m^2$ has a natural-number solution? | $3,914 | Number theory | open-research |  |
| Erdős problem 400 - part i | Can one show that $\sum_{n\leq x}g_k(n) \sim c_k x\log x$ for some constant $c_k$? | $3,914 | Number theory | open-research |  |
| Erdős problem 406 - one two | If we only allow the digits $1$ and $2$ then $2^{15}$ seems to be the largest such power of $2$. | $3,914 | Number theory | open-research |  |
| Erdős problem 409 - sigma termination | If $n > 1$ then the iteration $n\mapsto\sigma(n) - 1$ necessarily reaches a prime. Note: this is open — it is not clear that the σ iteration always terminates, since i… | $3,914 | Number theory | open-research |  |
| Erdős problem 410 | Let $σ_1(n) = σ(n)$, the sum of divisors function, and $σ_k(n) = σ(σ_{k-1}(n))$. Is it true that $\lim_{k → ∞} σ_k(n)^{\frac 1 k} = ∞$? This is problem (iii) from Erdo… | $3,914 | Number theory | open-research |  |
| Erdős problem 412 | Let $σ_1(n)=σ(n)$, the sum of divisors function, and $σ_k(n) = σ(σ_{k-1}(n))$. Is it true that, for every $m, n ≥ 2$, there exist some $i, j$ such that $σ_i(m) = σ_j(n)$? | $3,914 | Number theory | open-research |  |
| Erdős problem 413 - part i | Are there infinitely many barriers for `ω`? | $3,914 | Number theory | open-research |  |
| Erdős problem 414 | Let $h_1(n) = h(n)$ and $h_k(n) = h(h_{k-1}(n))$. Is it true, for any $m,n$, there exist $i$ and $j$ such that $h_i(m) = h_j(n)$? | $3,914 | Number theory | open-research |  |
| Erdős problem 428 | Is there a set $A\subseteq \mathbb{N}$ such that, for infinitely many $n$, all of $n-a$ are prime for all $a\in A$ with $0 < a < n$ and $$\liminf\frac{\lvert A\cap [1,… | $3,914 | Number theory | open-research |  |
| Erdős problem 445 | Is it true that, for any $c>1/2$, if $p$ is a sufficiently large prime then, for any $n\geq 0$, there exist $a,b\in(n,n+p^c)$ such that $ab\equiv 1\pmod{p}$? This is d… | $3,914 | Number theory | open-research |  |
| Erdős problem 454 | Is it true that `limsup (fun n => (f n - 2 * n.nth Prime : ℕ∞)) atTop = ⊤`? | $3,914 | Number theory | open-research |  |
| Erdős problem 455 | Let `q : ℕ → ℕ` be a strictly increasing sequence of primes such that `q (n + 2) - q (n + 1) ≥ q (n + 1) - q n`. Must `lim q n / (n ^ 2) = ∞`? | $3,914 | Number theory | open-research |  |
| Erdős problem 456 - part iii | Are there infinitely many primes $p$ such that $p-1$ is the only $n$ for which $m_n=p$? | $3,914 | Number theory | open-research |  |
| Erdős problem 458 | Let $\operatorname{lcm}(1, \dots, n)$ denote the least common multiple of $\{1, \dots, n\}$. Let $p_k$ be the $k$-th prime. Is it true that for all $k \geq 1$, $\opera… | $3,914 | Number theory | open-research |  |
| Erdős problem 463 | Is there a function $f$ with $f(n)\to\infty$ as $n\to\infty$ such that, for all large $n$, there is a composite number $m$ such that $$ n + f(n) < m < n + p(m) $$ Here… | $3,914 | Number theory | open-research |  |
| Erdős problem 479 | Is it true that, for every integer $k\neq 1$, there are infinitely many $n$ such that $2^n\equiv k\pmod{n}$? | $3,914 | Number theory | open-research |  |
| Erdős problem 495 | Let $\alpha,\beta \in \mathbb{R}$. Is it true that$$\liminf_{n\to \infty} n \\| n\alpha \\| \\| n\beta\\| =0$$? This is also known as the Littlewood conjecture. | $3,914 | Number theory | open-research |  |
| Erdős problem 517 | If `f(z) = ∑ aₖzⁿₖ` is an entire function (with `aₖ ≠ 0` for all `k`) such that `nₖ / k → ∞`, is it true that `f` assumes every value infinitely often? | $3,914 | Complex analysis | open-research |  |
| Erdős problem 535 | Let $r \geq 3$, and let $f_r(N)$ denote the size of the largest subset of $\{1,\ldots,N\}$ such that no subset of size $r$ has the same pairwise greatest common diviso… | $3,914 | Combinatorics, Number theory | open-research |  |
| Erdős problem 535 - first open case | The first open case of Erdős Problem 535 is $r = 3$: there should exist $c > 0$ such that $f_3(N) \leq N^{c/\log\log N}$ for all sufficiently large $N$. | $3,914 | Combinatorics, Number theory | open-research |  |
| Erdős problem 600 - part i | Let $r \geq 2$. Is it true that $e(n,r+1) - e(n,r) \to \infty$ as $n \to \infty$? | $3,914 | Combinatorics | open-research |  |
| Erdős problem 617 | Let $r\geq 3$. If the edges of $K_{r^2+1}$ are $r$-coloured then there exist $r+1$ vertices with at least one colour missing on the edges of the induced $K_{r+1}$. In… | $3,914 | Combinatorics | open-research |  |
| Erdős problem 624 | Let $X$ be a finite set of size $n$ and $H(n)$ be such that there is a function $f:\{A : A\subseteq X\}\to X$ so that for every $Y\subseteq X$ with $\lvert Y\rvert \ge… | $3,914 | Combinatorics | open-research |  |
| Erdős problem 647 | Let $\tau(n)$ count the number of divisors of $n$. Is there some $n > 24$ such that $$ \max_{m < n}(m + \tau(m)) \leq n + 2? $$ | $3,914 | Number theory | open-research |  |
| Erdős problem 672 | Can the product of an arithmetic progression of positive integers $n, n + d, ..., n + (k - 1)d$ of length ≥ 4, with $(n, d) = 1$, be a perfect power? | $3,914 | Number theory | open-research |  |
| Erdős problem 677 | Denote by $M(n, k)$ the least common multiple of the finite set $\{n+1, \dotsc, n+k\}$. Is it true that for all $m \geq n + k$, we get $M(m, k) \neq M(n, k)$? | $3,914 | Number theory | open-research |  |
| Erdős problem 680 - part i | Is it true that, for all sufficiently large $n$, there exists some $k$ such that $$ p(n+k)>k^2+1, $$ where $p(m)$ denotes the least prime factor of $m$? | $3,914 | Number theory | open-research |  |
| Erdős problem 680 - part ii | Can one prove this is false if we replace $k^2+1$ by $e^{(1+\epsilon)\sqrt{k}}+C_\epsilon$, for all $\epsilon>0$, where $C_\epsilon>0$ is some constant? | $3,914 | Number theory | open-research |  |
| Erdős problem 681 | Erdős problem 681. Is it true that for all large $n$ there exists $k$ such that $n + k$ is composite and $p(n+k) > k^2$, where $p(m)$ is the least prime factor of $m$ ? | $3,914 | Number theory | open-research |  |
| Erdős problem 686 - four | Can $4$ be written as $$4=\frac{\prod_{1\leq i\leq k}(m+i)}{\prod_{1\leq i\leq k}(n+i)}$$ for some $k≥2$ and $m≥n+k$? | $3,914 | Number theory | open-research |  |
| Erdős problem 686 - twenty five | Can $25$ be written as $$25=\frac{\prod_{1\leq i\leq k}(m+i)}{\prod_{1\leq i\leq k}(n+i)}$$ for some $k≥2$ and $m≥n+k$? | $3,914 | Number theory | open-research |  |
| Erdős problem 688 - part ii | In particular, is it true that $\epsilon_n = o(1)$? | $3,914 | Number theory | open-research |  |
| Erdős problem 695 | Let $q_1 < q_2 < \cdots$ be a sequence of primes such that $q_{i + 1} \equiv 1 \pmod{q_i}$. Is it true that $$ \lim_{k \to \infty} q_k^{1/k} = \infty? $$ | $3,914 | Number theory | open-research |  |
| Erdős problem 695 - upper Bound | Is there a sequence of primes $q_1 < q_2 < \cdots$ such that $q_{i + 1} \equiv 1 \pmod{q_i}$ and $$ q(k) \leq \exp(k (\log k)^{1 + o(1)})? $$ | $3,914 | Number theory | open-research |  |
| Erdős problem 699 | Erdős Problem 699. Is it true that for every $1 \le i < j \le n / 2$ there exists a prime $p \ge i$ with $p \mid \gcd\big(\binom{n}{i}, \binom{n}{j}\big)$? | $3,914 | Number theory | open-research |  |
| Erdős problem 723 - eq 12 | It is open whether there exists a projective plane of order 12. | $3,914 | Combinatorics | open-research |  |
| Erdős problem 749 | Let $\epsilon>0$. Does there exist $A\subseteq \mathbb{N}$ such that the lower density of $A+A$ is at least $1-\epsilon$ and yet $1_A\ast 1_A(n) \ll_\epsilon 1$ for al… | $3,914 | Number theory | open-research |  |
| Erdős problem 770 - part i | For every prime `p`, does the density of integers with `h n = p` exist? | $3,914 | Number theory | open-research |  |
| Erdős problem 770 - three | It is probably true that `h n = 3` for infinitely many `n`. | $3,914 | Number theory | open-research | 1 attempt(s) logged |
| Erdős problem 774 | Is every proportionately dissociated (infinite) set the union of a finite number of dissociated sets? | $3,914 | Combinatorics | open-research |  |
| Erdős problem 779 | A Conjecture of Marian Deaconescu, see p.120 in https://doi.org/10.2307/2975810 [Needed to index shift in order to avoid trivial case $n = 0$, where the conjecture is… | $3,914 | Number theory | open-research |  |
| Erdős problem 789 - sq | Let $h(n)$ be maximal such that if $A\subseteq \mathbb{Z}$ with $\lvert A\rvert=n$ then there is $B\subseteq A$ with $\lvert B\rvert \geq h(n)$ such that if $a_1+\cdot… | $3,914 | Combinatorics | open-research |  |
| Erdős problem 812 - part i | Is it true that $\frac{R(n+1)}{R(n)}\geq 1+c$ for some constant $c>0$, for all large $n$? | $3,914 | Combinatorics | open-research |  |
| Erdős problem 828 | Is it true that, for any $a \in \mathbb{Z}$, there are infinitely many $n$ such that $$\phi(n) \| n + a$$? | $3,914 | Number theory | open-research |  |
| Erdős problem 828 - lehmer conjecture | When $n > 1$, Lehmer conjectured that $\phi(n) \| n - 1$ if and only if $n$ is prime. | $3,914 | Number theory | open-research |  |
| Erdős problem 829 | Erdős Problem 829 (open). Let $A \subseteq \mathbb{N}$ be the set of perfect cubes. Is it true that $(1_A \ast 1_A)(n) \ll (\log n)^{O(1)}$? That is, does there exist… | $3,914 | Number theory | open-research |  |
| Erdős problem 835 | Does there exist a $k>2$ such that the $k$-sized subsets of {1,...,2k} can be coloured with $k+1$ colours such that for every $A\subset \{1,\ldots,2k\}$ with $\lvert A… | $3,914 | Combinatorics | open-research |  |
| Erdős problem 849 | Is it true that, for every integer $t\geq1$, there is some integer $a$ such that ${n \choose k} = a$ with $1\leq k \le \frac{n}{2}$ has exactly $t$ solutions? | $3,914 | Number theory | open-research |  |
| Erdős problem 853 - part i | Let $d_n = p_{n+1} - p_n$, where $p_n$ is the $n$th prime. Let $r(x)$ be the smallest even integer $t$ such that $d_n = t$ has no solutions for $n \le x$. Is it true t… | $3,914 | Number theory | open-research |  |
| Erdős problem 853 - part ii | Let $d_n = p_{n+1} - p_n$, where $p_n$ is the $n$th prime. Let $r(x)$ be the smallest even integer $t$ such that $d_n = t$ has no solutions for $n \le x$. Is it true t… | $3,914 | Number theory | open-research |  |
| Erdős problem 873 | Let $A = \{a_1 < a_2 < \dots\} \subseteq \mathbb{N}$ and let $F(A,X,k)$ count the number of $i$ such that $[a_i,a_{i+1}, \dots ,a_{i+k−1}] < X$, where the left-hand si… | $3,914 | Number theory | open-research |  |
| Erdős problem 885 | Is it true that, for every $k \geq 1$, there exist integers $N_1 < \dots < N_k$ such that $\|\cap_i D(N_i)\| \geq k$? | $3,914 | Number theory | open-research |  |
| Erdős problem 886 | Let $\epsilon>0$. Is it true that, for all large $n$, the number of divisors of $n$ in $(n^{1/2},n^{1/2}+n^{1/2-\epsilon})$ is $O_\epsilon(1)$? Erdős attributes this c… | $3,914 | Number theory | open-research |  |
| Erdős problem 889 | Let $v(n,k)$ count the prime factors of $n+k$ which do not divide $n+i$ for $0\leq i < k$. Is it true that $v_0(n)=\max_{k\geq 0}v(n,k)\to \infty$ as $n\to \infty$? | $3,914 | Number theory | open-research |  |
| Erdős problem 889 - general | Let $v_l(n) = \max_{k\geq l} v(n,k)$. For every fixed $l$, $v_l(n) \to \infty$ as $n \to \infty$ [ErSe67] Erdős, P. and Selfridge, J. L., Some problems on the prime fa… | $3,914 | Number theory | open-research |  |
| Erdős problem 890 - part a | If $\omega_k(n)$ counts the number of distinct prime factors of $n$ which are $>k$, then is it true that, for every $k\geq 1$, $$\liminf_{n\to \infty}\sum_{0\leq i < k… | $3,914 | Number theory | open-research |  |
| Erdős problem 890 - part b | Is it true that $$\limsup_{n\to \infty}\left(\sum_{0\leq i < k}\omega(n+i)\right) \frac{\log\log n}{\log n}=1,$$ where $\omega$ counts the number of distinct prime fac… | $3,914 | Number theory | open-research |  |
| Erdős problem 891 | Let $2=p_1 < p_2 < \cdots$ be the primes and $k\geq 2$. Is it true that, for all sufficiently large $n$, there must exist an integer in $[n,n+p_1\cdots p_k)$ with $>k$… | $3,914 | Number theory | open-research |  |
| Erdős problem 893 | Does the limit $\lim_{n\to\infty} \frac{f(2n)}{f(n)}$ tend to infinity? (Other finite limits have been ruled out by [KoLu25], see below) | $3,914 | Combinatorics | open-research |  |
| Erdős problem 912 | Prove that there exists some $c>0$ such that $$h(n) \sim c \left(\frac{n}{\log n}\right)^{1/2}$$ as $n\to \infty$. | $3,914 | Number theory | open-research |  |
| Erdős problem 912 - tao | A heuristic of Tao using the Cramér model for the primes suggests this is true with $c=\sqrt{2\pi}$. | $3,914 | Number theory | open-research |  |
| Erdős problem 913 - infinite many 8 p sq sub one primes | It is likely that there are infinitely many primes $p$ such that $8p^2 - 1$ is also prime. | $3,914 | Number theory | open-research |  |
| Erdős problem 930 | Is it true that, for every $r$, there is a $k$ such that if $I_1,\ldots,I_r$ are disjoint intervals of consecutive integers, all of length at least $k$, then $$ \prod_… | $3,914 | Number theory | open-research |  |
| Erdős problem 931 | Let $k_1 \geq k_2 \geq 3$. Are there only finitely many $n_2\geq n_1 + k_1$ such that $$ \prod_{1\leq i\leq k_1}(n_1 + i)\ \text{and}\ \prod_{1\leq j\leq k_2} (n_2 + j… | $3,914 | Number theory | open-research |  |
| Erdős problem 932 | Let $p_k$ denote the $k$th prime. For infinitely many $r$ there are at least two integers $p_r < n < p_{r+1}$ all of whose prime factors are $< p_{r + 1} - p_r$. | $3,914 | Number theory | open-research |  |
| Erdős problem 933 | If $n(n+1)=2^k3^lm$, where $(m,6)=1$, then is it true that $\limsup_{n\to \infty} \frac{2^k3^l}{n\log n}=\infty$? | $3,914 | Number theory | open-research |  |
| Erdős problem 936 - factorial add one | Is $n! + 1$ powerful for finitely many $n$? | $3,914 | Number theory | open-research |  |
| Erdős problem 936 - factorial sub one | Is $n! - 1$ powerful for finitely many $n$? | $3,914 | Number theory | open-research |  |
| Erdős problem 936 - two pow add one | Is $2^n + 1$ powerful for finitely many $n$? | $3,914 | Number theory | open-research |  |
| Erdős problem 936 - two pow sub one | Is $2^n - 1$ powerful for finitely many $n$? | $3,914 | Number theory | open-research |  |
| Erdős problem 942 | Is there some constant $c > 0$ such that $h(n) < (\log n)^{c + o(1)}$ and, for infinitely many $n$, $h(n) > (\log n)^{c - o(1)}$. | $3,914 | Number theory | open-research |  |
| Erdős problem 943 | Let $A$ be the set of powerful numbers. Is is true that $1_A\ast 1_A(n)=n^{o(1)}$ for every $n$? | $3,914 | Number theory | open-research |  |
| Erdős problem 945 | Is it true that $F(x) \leq (\log x)^{O(1)}$? | $3,914 | Number theory | open-research |  |
| Erdős problem 949 | Let $S \subseteq \mathbb{R}$ be a set containing no solutions to $a + b = c$. Must there be a set $A \subseteq \mathbb{R} \setminus S$ of cardinality continuum such th… | $3,914 | Combinatorics | open-research |  |
| Erdős problem 950 - part i | Is it true that $\liminf f(n)=1$? | $3,914 | Number theory | open-research |  |
| Erdős problem 950 - part ii | Is it true that $\limsup f(n)=\infty$? | $3,914 | Number theory | open-research |  |
| Erdős problem 950 - part iii | Is it true that $f(n)=o(\log\log n)$ for all $n$? | $3,914 | Number theory | open-research |  |
| Erdős problem 951 | If `1 < a 0 < ...` has property `Erdos951Prop`, is it true that `#{a i ≤ x} ≤ π x`? | $3,914 | Number theory | open-research |  |
| Erdős problem 962 | Main conjecture: $\log k(n) \le (\log n)^{(1/2 + o(1))}$ | $3,914 | Number theory | open-research |  |
| Erdős problem 972 | Erdős problem 972. Let $\alpha > 1$ be irrational. Are there infinitely many primes $p$ such that $\lfloor p\alpha \rfloor$ is also prime? | $3,914 | Number theory | open-research |  |
| Erdős problem 975 | For an irreducible polynomial $f \in \mathbb{Z}[x]$ with $f(n) \ge 1$ for sufficiently large $n$, does there exists a constant $c = c(f) > 0$ such that $\sum_{n \le x}… | $3,914 | Number theory | open-research |  |
| Erdős problem 979 | Let $k ≥ 2$, and let $f_k(n)$ count the number of solutions to $n = p_1^k + \dots + p_k^k$, where the $p_i$ are prime numbers. Is it true that $\limsup f_k(n) = \infty$? | $3,914 | Number theory | open-research |  |
| Erdős problem 982 | If $n$ distinct points in $\mathbb{R}^2$ form a convex polygon then some vertex has at least $\lfloor\frac{n}{2}\rfloor$ different distances to other vertices. | $3,914 | Convex/discrete geometry | open-research |  |
| Erdős problem 985 | Is it true that, for every prime $p$, there is a prime $q \leq p$ which is a primitive root modulo $p$? | $3,914 | Number theory | open-research |  |
| Erdős problem 1003 | Are there infinitely many solutions to $\phi(n) = \phi(n+1)$, where $\phi$ is the Euler totient function? | $3,914 | Number theory | open-research | 1 attempt(s) logged |
| Erdős problem 1049 | Let $t>1$ be a rational number. Is $\sum_{n=1}^\infty\frac{1}{t^n-1}=\sum_{n=1}^\infty \frac{\tau(n)}{t^n}$ irrational, where $\tau(n)$ counts the divisors of $n$? A c… | $3,914 | Number theory | open-research | 1 attempt(s) logged |
| Erdős problem 1056 | Let $k ≥ 2$. Does there exist a prime $p$ and consecutive intervals $I_0,\dots,I_k$ such that $\prod\limits_{n{\in}I_i}n \equiv 1 \mod n$ for all $1 \le i \le k$? | $3,914 | Number theory | open-research |  |
| Erdős problem 1060 - part ii | Part (ii) of Erdős Problem 1060: bound on the number of $k \le n$ with $k \sigma_1(k) = n$. | $3,914 | Number theory | open-research |  |
| Erdős problem 1068 | Does every graph with chromatic number $\aleph_1$ contain a countable subgraph which is infinitely connected? | $3,914 | Combinatorics | open-research |  |
| Erdős problem 1072 - part i | Is it true that there are infinitely many $p$ for which $f(p) = p − 1$? | $3,914 | Number theory | open-research |  |
| Erdős problem 1072 - part ii | Is it true that $f(p)/p \to 0$ for $p \to \infty$ in a density 1 subset of the primes? | $3,914 | Number theory | open-research |  |
| Erdős problem 1073 | Is it true that $A(x) \le x^{o(1)}$? | $3,914 | Number theory | open-research |  |
| Erdős problem 1082 - part i | Let $A\subset \mathbb{R}^2$ be a set of $n$ points with no three on a line. Does $A$ determine at least $\lfloor n/2\rfloor$ distinct distances? | $3,914 | Geometry | open-research |  |
| Erdős problem 1085 - upper d 3 | Is the $n^{4/3}\log\log n$ lower bound in 3D also an upper bound?. | $3,914 | Convex/discrete geometry | open-research |  |
| Erdős problem 1094 | For all $n\ge 2k$ the least prime factor of $\binom{n}{k}$ is $\le\max(n/k,k)$, with only finitely many exceptions. | $3,914 | Number theory | open-research |  |
| Erdős problem 1095 - log is Theta | Sorenson, Sorenson, and Webster [SSWE20] give heuristic evidence that $\log g(k) \asymp \frac{k}{\log k}$. | $3,914 | Number theory | open-research |  |
| Erdős problem 1095 - lower conjecture | Erdős, Lacampagne, and Selfridge [ELS93] write 'it is clear to every right-thinking person' that $g(k)\geq\exp(c\frac{k}{\log k})$ for some constant $c>0$. | $3,914 | Number theory | open-research |  |
| Erdős problem 1101 - part i | 1. Is there a good sequence with polynomial growth? | $3,914 | Number theory | open-research |  |
| Erdős problem 1106 - part ii | Let $p(n)$ be the partition number of $n$ and $F(n)$ be the number of distinct prime factors of $∏_{i= 1} ^ {n} p(n)$, $F(n)>n$ for sufficiently large $n$. | $3,914 | Number theory | open-research |  |
| Erdős problem 1107 | Let $r \ge 2$. Is every large integer the sum of at most $r + 1$ many $r$-powerful numbers? | $3,914 | Number theory | open-research |  |
| Erdős problem 1108 - part i | For each $k \geq 2$, does the set $A = \left\{ \sum_{n\in S}n! : S\subset \mathbb{N}\text{ finite}\right\}$ of all finite sums of distinct factorials contain only fini… | $3,914 | Number theory | open-research |  |
| Erdős problem 1113 - filaseta finch kozek | Filaseta–Finch–Kozek conjecture (2008). Every Sierpiński number is either a perfect power or possesses a finite covering set of primes. | $3,914 | Number theory | open-research |  |
| Erdős problem 1135 | The Collatz conjecture states that for any positive integer $n$, there exists a natural number $m$ such that the $m$-th term of the sequence is 1. | $3,914 | Number theory, Dynamical systems | open-research | Famous; ignore |
| Erdős problem 1137 | Let $d_n=p_{n+1}-p_n$, where $p_n$ denotes the $n$th prime. Is it true that $$\frac{\max_{n < x}d_{n}d_{n-1}}{(\max_{n < x}d_n)^2}\to 0$$ as $x\to \infty$? | $3,914 | Number theory | open-research |  |
| Erdős problem 1142 | Are there infinitely many $n > 2$ such that $n - 2^k$ is prime for all $k \geq 1$ with $2^k < n$? The only known such $n$ are $4, 7, 15, 21, 45, 75, 105$ (OEIS [A03966… | $3,914 | Number theory | open-research |  |
| Erdős problem 1175 | Let $\kappa$ be an uncountable cardinal. Must there exist a cardinal $\lambda$ such that every graph with chromatic number $\lambda$ contains a triangle-free subgraph… | $3,914 | Combinatorics | open-research |  |
| Erdős problem 1192 | Does there exist, for all $r\geq 2$, a basis $A$ of order $r$ (so that $f_r(n)>0$ for all large $n$) such that $$\sum_{n\leq x}f_r(n)^2 \ll x$$ for all $x$? | $3,914 | Combinatorics | open-research |  |
| Erdős problem 1203 | Prove that $F(n)\to \infty$ as $n\to \infty$. | $3,914 | Number theory | open-research |  |
| Erdős problem 1209 - part iii d | Are there $n$ such that $n+2^{2^k}$ is infinitely often squarefree? | $3,914 | Number theory | open-research |  |

## Snapshot sources

- Raw catalog snapshot: re-fetch with `curl "https://conjectures.io/v1/catalog/conjectures?limit=100&offset={0,100,200}"`.
- Solved/retired targets (30, not listed above) have `bounty.reason = ALREADY_SOLVED` in the same feed.
