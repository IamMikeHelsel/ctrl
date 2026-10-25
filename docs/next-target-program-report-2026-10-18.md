# Next mathematical target: program manager report

Date: 2026-10-18–19, America/Los_Angeles. Current checkpoint: complete seven-smooth restricted-family theorem kernel checked and independently source-audited; integrated build passed; eleven-smooth computational evidence; 740-run tremor batch complete without a qualifying new-method win.
AI disclosure: this report is written by the OpenAI Codex program manager subagent requested by
Mike. It distinguishes new-to-this-repository work from a potentially new mathematical result.

## Decision to make

The previous session improved the proof of an existing construction. The new request is to pursue
genuinely new mathematics. The first filter is therefore whether the proposed experiment could
cross a known mathematical boundary, not whether its code or formalization would be new here.

The current catalog is useful for navigation but not reliable enough for investment decisions.
Several tempting stepping stones already have stronger prior results or recent proof claims.

## Shortlist and reasons

| Target | Opportunity | PM recommendation |
| --- | --- | --- |
| 885, common factor differences | A finite table of factorizations could extend the known cases. | Excluded from this lane after discovering an existing active pod effort. Preserve that team's work. |
| 273, restricted covering systems | A finite strict covering would settle the positive direction; stronger structural capacity bounds could produce useful partial progress. | Preferred available lane. Benchmark a new fiber/overlap bound against prior exclusions before enlarging the search. A failed bounded search cannot settle nonexistence. |
| 1063, binomial divisibility | Stronger asymptotic bounds or new exact values. | Deprioritize: current primary source links an already-proved subexponential upper bound. Merely improving the old least-common-multiple bound would duplicate known work. |
| 319, irreducible signed reciprocal sums | Better asymptotic constant or certified finite extremal values. | Secondary at best. Linear growth is already known; exact-value formalization also needs a parameter-faithfulness review. |
| 647, divisor-count condition | A finite positive witness would settle the existential question. | Deprioritize blind range extension. Existing computational frontiers are already substantial, and a new small kernel-checked range would be verification work rather than mathematical novelty. |
| 1056, modular interval products | A finite witness can improve the known number of adjacent intervals, but cannot settle the all-parameter statement. | Do not target the catalog's suggested cases 4–6. Results through 14 intervals are already recorded. |
| 488, density of multiples | An exact finite counterexample would refute the universal statement. | Deprioritize pending review of an existing author's full refutation claim with Lean source. It cannot responsibly be treated as an untouched target. |

The recommendation is about certificate quality and avoiding known duplication; it is not a
calibrated probability of solving any target tonight.

The initial independent shortlist favored 885. Reading `work/pod/README.md` changed that decision:
885, 939, and MF-13 are already active in a concurrent research effort. Our lane will not duplicate
their searches or edit their files. This is a coordination decision, not evidence that those
mathematical directions are unpromising.

## Evidence that changed the ranking

The current Formal Conjectures source still marks the general 885 problem open and contains a
proved four-integer construction, attributed to Bremner's 2019 work. A five-integer construction
is therefore a meaningful candidate frontier, although absence of one from this file is not a
novelty proof. The publisher page was inaccessible in this pass, so the full paper has not yet
been independently read. [Formal Conjectures 885](https://raw.githubusercontent.com/google-deepmind/formal-conjectures/main/FormalConjectures/ErdosProblems/885.lean),
[Bremner publication record](https://experts.azregents.edu/en/publications/on-a-problem-of-erd%C3%B6s-related-to-common-factor-differences/).

For 273, the formal target is a **strict** covering: distinct moduli matter. An author's repository
claims structural exclusions and a partial formal reduction, rather than a solution. These claims
need review before choosing search bounds, but already warn against assuming that the obvious
small search is untouched. [Formal Conjectures 273](https://raw.githubusercontent.com/google-deepmind/formal-conjectures/main/FormalConjectures/ErdosProblems/273.lean),
[author's research repository](https://github.com/idealombrer/erdos-273-covering-pm1).

The root agent's primary-forum review found reported exact exclusions of least common multiples
below eight million and a prime cutoff of 877. These are research baselines to check and respect,
not results obtained in our session. A fresh scan below those thresholds would be replication.

The current 1063 source explicitly links a LEAP proof of a subexponential upper bound of the form
`exp[(k/log k)(log log k + log log log k + log 2)]`. The broad problem of estimating the least
value remains, but beating the old elementary bound is no longer a new milestone.
[Formal Conjectures 1063](https://raw.githubusercontent.com/google-deepmind/formal-conjectures/main/FormalConjectures/ErdosProblems/1063.lean).

For 319, the source already records linear growth and the lower constant `1−1/e`. Its exact-value
answer declaration is currently a natural number independent of `N`, although the requested
maximum depends on `N`; that needs review before adapting it as a frozen challenge. This is a
faithfulness concern, not a solution of the mathematical problem.
[Formal Conjectures 319](https://raw.githubusercontent.com/google-deepmind/formal-conjectures/main/FormalConjectures/ErdosProblems/319.lean).

For 647, a primary August 2026 preprint reports kernel-checked exclusion through one billion and
cites much larger non-kernel computational frontiers. Its stated contribution is the trust base,
not a new range record. Repeating a small enumeration would not satisfy the new research goal.
[Mian and Siddique, arXiv:2608.17880](https://arxiv.org/abs/2608.17880).

For 1056, OEIS records fourteen terms, ending with prime 10,428,007, and credits Andersen's 2007
extension. The catalog's cases 4–6 are not new search territory.
[OEIS A060427](https://oeis.org/A060427).

For 488, the author's September 2026 package claims a refutation of the precise unrestricted
statement, with an adapter to Formal Conjectures, source, and a reported independent kernel run.
The author still seeks specialist review and priority checking. We have inspected the claim,
not reproduced its verification; the claim is enough to disqualify casual novelty assertions.
[Gessel's source and disclosure](https://gist.github.com/declangessel/d8e15e5ff1b6c7e99e3d86d7c66f1d08).

Direct access to several erdosproblems.com pages returned HTTP 403. No text from those pages was
copied into the repository. Primary source and author artifacts above provide the usable evidence;
catalog status alone is not treated as definitive proof of the research frontier.

## What a successful experiment must produce

For 273, a positive witness must list distinct admissible moduli and one residue class for each,
prove the prime-minus-one condition, and cover every residue of their least common multiple.
An exclusion result must state precisely which moduli or period family it excludes and provide
a certificate that a separate exact checker can replay. Search-model infeasibility by itself
does not prove the original mathematical statement.

One cheap theoretical test already rules out a tempting approach. Suppose we assign nonnegative
weights of total `W` to the residues modulo a common period, and bound each modulus by the largest
weight of any one of its residue classes. For modulus `m`, this maximum is at least its class
average `W/m`. Summing those maxima therefore cannot improve the ordinary reciprocal-density
test. If the reciprocal sum is already at least one, this unconditioned weighted-union bound
cannot exclude a covering. This is a direct averaging argument, not yet a Lean-checked result in
this session. A stronger approach must retain conditional assignments or unavoidable overlaps.

A failed search is useful only when its domain is explicit. Report searched ranges or parameter
families, candidate counts, the strongest near-witness, and the reason for the next experiment.
Do not report “no solution” when the result is only “no witness in this bounded family.”

## Resource and stopping decisions

Spark is appropriate after a local benchmark demonstrates a well-defined, parallelizable search
and a small independent checker. Use `ctrl spark` and preserve existing jobs and artifacts. More
compute should enlarge a justified search domain or discriminate between hypotheses, not repeat
an already-understood failure.

No novelty claim is made at this checkpoint. The root agent selected 273; this report records
experiment outcomes and why each continuation or pivot was chosen.

## Selected promising experiment: an entire smooth-modulus family

The root agent is investigating a stronger target than extending a finite period scan: exclude
every finite covering whose admissible moduli have prime factors only in `{2,3,5,7}`, with no
bound on their exponents. A finite-period exclusion alone does not establish this.

The proposed certificate has two independently checkable parts. A small finite prefix of moduli
has maximum possible coverage at most `α`, regardless of its residue choices. The reciprocal sum
of all remaining admissible smooth moduli is at most `T`. If `α+T<1`, every finite covering drawn
from the whole family misses positive density. The finite prefix captures unavoidable overlap;
the tail uses a safe union bound. Bounding the tail over all smooth integers rather than only
shifted primes is conservative, and a box of exponent bounds gives an exact product of geometric
series for its complement.

This route passes the first conceptual check: it avoids the failed unconditioned weighted-union
bound by proving an integer overlap loss in the prefix. It also avoids exchanging limits of
infinite unions: the theorem concerns arbitrary **finite** candidate coverings, whose tail
contribution is bounded by the same `T`.

Prior-art review of the author's manuscript and scripts did not locate a seven-smooth-family
exclusion. Its seven-smooth figure is a finite reciprocal-mass profile. Its open questions say
that a sharper certified coverage bound for the three-smooth subfamily was not established.
The associated script uses greedy choices despite printing “MAX” and “optimal”; its output is
a candidate construction's coverage, not a universal upper bound. This is a reason to inspect
the proof mechanism rather than inherit labels.
[Manuscript](https://raw.githubusercontent.com/idealombrer/erdos-273-covering-pm1/master/PAPER_273.tex),
[greedy script](https://raw.githubusercontent.com/idealombrer/erdos-273-covering-pm1/master/scripts/landscape_pierpont_subpool.py).

The source also makes an unsupported parity inference: disjoint use of small moduli 2 and 3
does not force one of the two parity subcovers to omit both; they could be assigned to different
halves. Our proposed certificate will not depend on that inference. None of these observations
by itself resolves 273, and the prior-art search is not exhaustive enough to assert novelty.

The first seven-smooth experiment passed exact Python checking. The prefix is `{4,6,10,12}`
with base period 60. For each remaining modulus `m`, set `g=gcd(m,60)`. Its possible coverage of
the prefix's uncovered residues is bounded by the largest uncovered count in any class modulo
`g`, multiplied by `g/(60m)`. This is the exact Chinese-remainder density for a fixed class,
maximized to permit every remaining modulus its most favorable placement.

The implementation retained 1,230 moduli after safe Fermat filtering in the exponent box
`a≤14, b≤9, c≤6, d≤5`, with `a≥1`, and bounded all omitted even smooth moduli by the exact
geometric tail `63853284893/294055272000000`, approximately `0.0002171472`. The raw reciprocal
bound is about `1.06745`, so ordinary counting cannot exclude this family.

The PM independently rewrote the check using lists of residues, with no bit masks, no pruning,
and no import of the implementation. All 720 normalized prefix assignments passed. The smallest
uncovered-density margin was exactly
`270244625213/21003948000000 ≈ 0.01286637`, attained at residues `(0,1,1,3)` for the listed prefix.
That is a 1.2866-percentage-point margin. This check ran in about 0.12 seconds; it does not need
Spark. The implementation's smaller pruned tree agrees with the independent exhaustive check.

For formalization, the root agent simplified the seven-smooth certificate to the smaller exponent
box `a≤10, b≤6, c≤4, d≤3`. Its geometric tail is below `5/1000`. The remaining reciprocal masses,
grouped by gcd with 60, are bounded by the following small rational numbers:

| gcd | 4 | 6 | 10 | 12 | 20 | 30 | 60 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| mass upper bound | 120/1000 | 101/1000 | 21/1000 | 85/1000 | 47/1000 | 56/1000 | 40/1000 |

The PM independently rebuilt that smaller pool and checked each rational bound, the geometric
tail, and all 720 prefix assignments. Even after these conservative roundings, the minimum
density margin is `342/60000 = 0.0057`. The smaller box is essential to the stated mass table:
the larger original box has slightly more mass in the gcd-12 group. This distinction was checked
explicitly so the finite certificate cannot silently inherit the wrong analytic bridge.

The first eleven-smooth extension failed to establish exclusion: prefix
`{4,6,10,12,16,18}` left 8,280 unresolved leaves, with worst bound excess about `0.02123`.
This was a failure of that bound, not a covering witness or proof of coverability.

Adding 30 and 36 to the prefix succeeded. The resulting period is 720, with exponent caps
`[14,9,6,5,4]` for primes `[2,3,5,7,11]`. The retained pool has 5,265 moduli; its exact omitted
tail is `1806085527193/7116137582400000`. Ordinary reciprocal counting still fails: its bound
is about `1.17483`. Conditional capacity checking nevertheless closes every branch.

The baseline search, with only the first residue fixed by translation, visited 594,323 states
and closed 561,900 by capacity bounds in about 75.6 seconds. A translation-stabilizer optimization
reduced this to 3,518 states and 3,271 bound closures in about 0.54 seconds, with no unresolved
leaves in either run. These counts and timings are recorded in `work/273/probe-11-deep.json`
and `work/273/probe-11-symmetric.json`; they are local measurements, not general performance
guarantees. The optimization is mathematically justified by translations that preserve all
previously selected classes: for the next modulus `m`, residue representatives below
`gcd(previous lcm,m)` suffice. The independent seven-smooth check did not need this optimization.

A deeper eleven-smooth Spark experiment was dispatched through `ctrl spark` before the local
optimization made this family cheap. Its job ID is `20261019-052014-273-solve-8226`; no result
from that job supports the mathematics: it failed immediately because the root agent accidentally
included modulus 48 in the prefix, although 49 is composite. The input assertion caught the
mistake. This is an execution error, not a failed mathematical bound. The corrected next
exploration is thirteen-smooth, while the smaller
seven-smooth finite core is the first formalization target. The reason for separating these
efforts is practical: a small trusted core can validate the method while exploration tests
whether it extends to a stronger family.

The PM saved an independently written replay at `work/273/check_seven.py`. For the finite box
it replaces the Fermat filter with trial division by primes 3 through 97: discard `m` only when
one of these primes divides `m+1` and is not equal to it. Every prime `m+1` survives, while any
surviving composite can only weaken the upper bound. The sieve retains 616 moduli. Exact grouped
fractions still fit the same coarse mass table; the tail is `632647/133358400 < 5/1000`.
All 720 assignments reproduce the margin `342/60000`. The checker also rejects four corruptions:
an understated group mass, an overstated minimum margin, a negative weight, and a missing group.
Run `uv run python work/273/check_seven.py --self-test`; optional `--output PATH` saves its JSON
audit. It imports no search implementation and uses neither masks nor search pruning.

The root agent subsequently obtained successful kernel checks for four substantial proof
components, with only permitted axioms:

| Component | Checked result | Remaining boundary |
| --- | --- | --- |
| `CoveringMass.lean` | Prime inputs survive the divisor sieve; all finite grid divisions are exact; gcd groups are complete; all seven mass bounds hold. | Connect these list computations to the arbitrary covering's chosen moduli. |
| `CoveringTail.lean` | The four-dimensional reciprocal weight has sum `35/16`; the finite box has its exact mass; **every finite set** of exponent tuples outside the box has mass at most `632647/133358400`. | Relate the covering's distinct moduli to their exponent tuples. |
| `CoveringCRT.lean` | One congruence class meets a periodic surviving set in at most the gcd-compatible fiber count times the number of periods; `lift_card` proves exact cardinality across repeated periods. | Assemble these estimates over the covering's common period. |
| `CoveringCapacity.lean` | All 720 normalized assignments satisfy the scaled margin 342; large-fiber universal bounds and `uncovered_of_scaled_certificate` pass. | Supply the full covering's concrete capacity bounds to this abstract certificate. |

The PM read these statements and found their scope consistent with the proposed argument. This
is a statement review, not an independent re-run of their Lean builds. The infinite tail lemma
was proved rather than extrapolated from a finite cutoff. At this earlier component checkpoint,
the full exclusion was unassembled. The completed theorem is recorded below; eleven-smooth
remains Python evidence.

The finite capacity computation was slow in the kernel. The root agent reduced its work by
replacing the fiber maxima for gcds 20, 30, and 60 with universal bounds 3, 2, and 1. Together with
the tail these contribute the constant 8,880. The PM added a second check to the independent
validator: the original and the coarser bound both have minimum scaled margin 342 across all
720 assignments. This simplification preserves enough margin while reducing kernel arithmetic.
The integrated `lake build` completed successfully with 8,970 jobs, including all four supporting
modules and the research root. The finite capacity module took about 41 seconds. Every printed
axiom set for the new modules is permitted; `work/273/checkpoint.json` records the checkpoint.

The local thirteen-smooth search hit its two-million-state limit without a conclusion. A corrected
Spark run, `20261019-052643-273-solve-298c`, used a valid prefix including modulus 28 and a
240-second budget. Its fetched result reports `completion=time_limit`: 89,700 nodes, 57,567
pruned, and 26,952 unresolved after 240.1187 seconds. The process completed successfully, but
the mathematics remains inconclusive. Reaching a resource limit is neither an exclusion nor a
positive witness. Further frontier computation is lower priority than finishing the existing
seven-smooth proof assembly.

Latest validation reported by the root agent: 106 Python tests pass, with one integration test
deselected. Targeted Ruff checks for the experiments, problem 273, and our tests pass. The
concurrently changing whole tree now has 495 Ruff findings and 71 files needing formatting,
including other agents' work; the earlier 119-finding snapshot is superseded. Those files are
preserved, and the whole-repository check is not represented as passing. The PM checker
separately passed Ruff, formatting, exact replay, and its four rejection tests after the
coarser-bound extension.

`ctrl check --all` confirms the existing 834 solution builds, audits, and binds to its precise
challenge, but it remains `NOT_APPROVED`. Problem 273 is skipped because no completed solution
is declared. These states are intentional and are not silently promoted to a successful full
proof or human approval.

Mike initially objected to automatic hourly reminders, and the root agent paused that schedule.
Mike subsequently **explicitly authorized specific overnight self-check-ins**. The existing
automation `erd-s273-overnight-proof-and-review` is now saved ACTIVE for 23:30 October 18 and
01:30, 04:30, and 07:30 October 19, all Pacific. Its hard end is October 19 at 14:30 UTC.
It pauses immediately if work is complete, canceled, superseded, or no longer actionable,
never extends itself, and reports only material changes. This finite authorization replaces
the earlier paused state; it does not authorize indefinite or dead-thread recurrence.
The final update explicitly includes 07:30 delivery of the PM morning report. If research
finishes early, only that delivery checkpoint remains; idle interim wakeups are removed.
Completion includes report delivery, and the hard end remains unchanged.

Scheduling audit, October 19: the 00:27 Pacific wake was off schedule and produced no research
change. Independent inspection of the installed scheduler confirmed that the end-date field
bypasses its local-time scheduling path, while recurring rules can jitter by five minutes.
The root corrected this to a single occurrence; tool confirmation and its database read show
actual and nominal next-run times both **01:30 Pacific on October 19**. This checkpoint retains
bounded reversal/reset work. Later 04:30/07:30 checkpoints require explicit same-day re-arming,
with elapsed-time/date guards and an early-completion skip to morning delivery. Only 01:30
is currently verified; future wakes depend on the app being awake and successful re-arming.
The PM changed no automation and performed no new research during this audit.

Mike renewed the active work request: finish the seven-smooth theorem, then push the robot-tremor
experiments and explain the morning results. This sets the priority within the finite schedule;
eleven-smooth is secondary. The ongoing morning report is
`work/vision/morning-report-2026-10-19.md`. A missing proof step is not recorded as a false
theorem, and a successful simulation will not be recorded as hardware acceptance.

The earlier integrated build is recorded evidence. When a generated `CoveringCapacity.olean`
was later missing, the root agent rebuilt that target successfully with permitted axioms before
continuing assembly. That earlier incomplete checkpoint has now been superseded by the full
theorem verification below.

The next bridge, `CoveringAssembly.pool_capacity_bound`, now compiles and prints only
`propext`, `Classical.choice`, and `Quot.sound`. For arbitrary surviving residue set `U`, it
bounds the finite reciprocal pool plus the tail allowance 0.3 by
`scaledRemainderCapacity U / 1000`. This connects the finite mass calculations to the capacity
expression. It was the last mass bridge before full family assembly, rather than the family
theorem itself.

Current result: the full restricted-family theorem in `CoveringFamily.lean` passes direct Lean
compilation, exit code zero. Both `seven_smooth_period_gap` and `seven_smooth_not_cover` print
only `propext`, `Classical.choice`, and `Quot.sound`. The PM independently read
the complete path and found its final statements faithful: arbitrary finite distinct moduli,
integer residues, unrestricted smooth exponents, derived evenness, no hidden capacity
assumptions, and a positive common period in the existence wrapper. The density statement
counts the shifted common-period interval at margin `57/10000`. The direct kernel check and
independent source audit close the full restricted-family proof gate. The integrated-project
build subsequently passed with 8,972 jobs. This does not solve problem 273, and mathematical
priority remains unestablished. Robot-tremor experiments are now the active priority;
eleven-smooth remains secondary. The first 40-run pilot passes six numerical convergence
checks but shows no new smoothness win at the declared matched-lag threshold. The PM identified
noise/timing confounding in two proposed stress cases and requested a noise-only control before
the larger batch. Detailed results and source-review limitations are in the morning report.

The corrected batch is now complete: 740 runs across 74 case/seed traces, with ten seeds for
stochastic cases and one for each deterministic case. The PM independently verified source
hash consistency, finite metrics, no planner failures, six passing convergence checks, and
162 exact fresh/Ruckig equality checks without expiration. Pure camera jitter benefits from
the known actual-time correction: mean paired jerk reduction 71.59%, falling to 7.61% with
measurement noise. The freshness rule has zero qualifying wins against Ruckig, including
cross-parameter comparisons, under the declared 20% jerk/5% tracking/1 ms lag gate. This
supports practical diagnosis, not a new controller or a claim that most robot tremor is timing.
The frozen saved source retains its original empty-convergence behavior; the six checks in
this batch are unaffected. The current implementation now fixes it, as recorded below.

The follow-up directly tests finite-difference velocity feedback at 1 kHz: 248 runs, both
source hashes verified, eight convergence checks passing, and no nonfinite metrics. With pure
servo jitter, actual intervals reduce jerk by 99.02% for the ideal reference and 92.16% for
Ruckig relative to nominal intervals. With jitter plus encoder noise, actual intervals plus
a standard 100 Hz filter reduce jerk about 78%. All ten paired seeds pass the declared
tracking/lag/jerk gate for those comparisons. This is a known correction demonstrated in a PD
model, not a new algorithm, full PID validation, or evidence of cause prevalence in hardware.

The current simulator now correctly reports absent convergence checks as “not run”; its frozen
740-run source remains unchanged. An exact-rational reference timing sink has been added,
with a kernel-checked conditional uncertainty formula and no actuator API. The PM found two
guard holes (NaN sequence values and reused clock epochs), reproduced them, and reviewed the
repairs: strict integer counters and strictly increasing epochs, with new regression tests.
The timing algebra's integrated build passed; no closed-loop safety, passivity, novelty,
or hard-real-time guarantee is claimed. The morning report includes both positive and negative
experimental results and explains why the direct-feedback test changed the interpretation.

Final checkpoint: integrated Lean build 8,973 jobs; 164 Python tests pass, one deselected,
in 1.69 seconds; targeted Ruff/format pass on 16 files. Whole-tree Ruff has 1,054 findings in
concurrent `work/pod` and formatting flags 110 concurrent files, preserved rather than swept
into this work. `ctrl check --all` verifies 834 build, token audit, permitted axioms, and exact
binding, with only `NOT_APPROVED`; 273 is not presented as an approved full-problem solution.
No challenge files changed. The PM independently passed 12 focused guard/simulator regressions.
Reproduction instructions are in `work/vision/reproduce.md`.

At the scheduled 01:30 checkpoint the PM verified all saved theorem/current-artifact hashes
and the three frozen simulator-source hashes; no proof build or numerical batch was repeated.
The reversal/reset source audit emphasizes that reset clears stored observations but cannot
revoke previously returned predictions, overlapping capture intervals do not establish true
time order, and reversal enclosure requires co-temporal position/velocity error bounds plus
a valid acceleration remainder over the full prediction interval. Hidden model violations
may remain undetectable. The bounded exact event replay is now independently verified.

The 01:30 continuation found and repaired one further ordering defect: adjacent interval
overlap could erase constraints from earlier accepted samples. A cumulative maximum lower
endpoint now tests whole-history feasibility and clears on reset. The PM verified saved
source hashes and independently recalculated every ready query in the analytic cubic reversal
trace: 1,813 ready predictions, zero misses for valid acceleration bound 4, and 120 undetected
misses for deliberately false bound 0. A separate reachable-set oracle agrees on 3,000
decisions across 1,000 interval chains and checks unchanged state on rejection and clearing
on reset. The first harness lacked a no-state query because new data arrived immediately at
reset; a disclosed 10 ms delay fixes that coverage fixture. No physical or closed-loop claim
is made, and this analytic replay is not added to the existing 988 plant comparisons.
Bounded research is complete; only routine checkpoint checks and morning delivery remain.

Updated 01:30 checks: 201 tests pass, one deselected, in 7.77 seconds across the concurrently
expanded suite; the nine timing-sink tests take 0.03 seconds. The full suite exceeds the
approximately five-second target and is not represented otherwise. Ruff/format pass for the
three changed Python files. Whole-tree Ruff has one unrelated finding in
`tests/test_skew_normal_form.py`; formatting flags eight files. These replace the earlier
large concurrent-tree warning counts. No unrelated files were changed to make this work appear clean.

Final bounded-work checkpoint: the refreshed replay source hashes match and numerical outcomes
are unchanged after the ordering-assumption docstring clarification. Thirteen focused tests
pass in 0.02 seconds. `ctrl check --all` exits 3 solely for 834 `NOT_APPROVED`; its build,
audit, and binding pass, and 273 is not represented as a full challenge solution. Routine work
is finished. The automation tool and root's database verification confirm **only October 19
07:30 Pacific** remains, with actual and nominal times equal; 04:30 is removed. That occurrence
delivers the morning report and pauses, with no further re-arming or new research batch.

The follow-up novelty review is saved in `work/273/novelty-review.md`. It found explicit prior art
for optimized prefix coverage plus a reciprocal remainder bound, so that broad method is not
claimed as new. The exact seven-/eleven-smooth prime-minus-one exclusions were not located.
Inspected general divisibility and minimum-modulus theorems do not immediately imply them;
this remains a scoped search result, not a priority determination. The user requested completion
of the full seven-smooth theorem and novelty review before advancing the eleven-smooth proof.

If the eleven-smooth bridge is completed, its simple mathematical consequence would be that any
covering in problem 273 needs a modulus with a prime factor at least 13. This differs from a
lower bound on the largest modulus: it restricts the allowed prime factors even when their
exponents are arbitrarily large. It would be partial progress, not a resolution of the problem.

## What worked, what failed, and how to ask next

What worked was changing the object being bounded. Counting all available class densities loses
their forced overlap; conditioning on a few residue choices retains enough overlap to exclude
a whole infinite modulus family. The first eleven-smooth prefix failed because its bound was
too loose; adding two classes supplied enough structure to close it. Translation symmetry then
reduced the amount of computation needed without changing the mathematical question.

The seven-smooth bridge is complete. A useful mathematical follow-up is:

> Extend the completed proof to the eleven-smooth computational certificate and independently
> audit the resulting statement. Check the specific family restriction against prior work.
> Keep computational evidence, formal proof, and priority claims separate; explain each remaining
> gap and whether additional compute would address it. Do not repeat the completed seven-smooth proof.

For the practical robotics priority, request offline validation against real recorded telemetry
with verified provenance, units, timestamp meanings, and command semantics. Exercise cached
prediction invalidation and resets at the consumer boundary, use matched-lag baseline
comparisons, and preserve failed cases. Physical robot control needs a separately defined scope.
These requests target the remaining evidence gaps rather than merely enlarging a search.

## Concrete controls-data lead

The user expanded the program to three connected lanes: (1) complete and review the seven-smooth
theorem, then eleven-smooth if it holds; (2) select and test ten robotics/vision research targets;
(3) develop practical middleware for smoother research robots. The ten-target selection and
source-backed experiment gates are in `work/vision/portfolio.md`. Initial practical priorities
are acquisition-time uncertainty, irregularly sampled visual velocity, and freshness-aware
jerk-limited command reconstruction.

The user's timing/mistuning explanation for robot tremor is treated as a hypothesis, not an
established majority cause. The experiment plan compares timing effects with friction,
saturation, resonance, and estimator resets, and requires matched lag/bandwidth. Ruckig,
MoveIt Servo, Kalibr/VersaVIS, and ROS 2 timing diagnostics already address parts of the problem;
the middleware must demonstrate what its explicit contracts add. Smoother commands alone do
not establish stable, passive, safer, or more accurate physical motion.

Mike suggested the Rerun community as a source of real robot data. Official examples expose DROID
joint states, camera streams, and teleoperator position/velocity commands, while ROS and MCAP
integration can carry timestamped recordings. These are practical inputs for measuring tracking
error and sample timing, and for testing the earlier certificate assumptions.
[DROID example](https://rerun.io/examples/robotics/droid_dataset),
[MCAP integration](https://docs.rerun.io/dev/howto/logging-and-ingestion/mcap/).

Recorded demonstrations are not automatically a live robot connection, nor do observed residuals
establish a worst-case disturbance bound. The next useful controls experiment would select one
recording with its robot model, units, timestamps, and command semantics, then compare commanded
and realized motion. No data download or hardware validation is claimed here.
