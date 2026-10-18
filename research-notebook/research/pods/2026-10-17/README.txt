THREE RESEARCH PODS — 17 October 2026

User authorization: controls, Erdos and Weinstein pods, each with an independent
progress grader. The remaining weekly allotment and up to half of available cloud
credits may be used only while work is productive. The visible Codex credit balance
is recorded in budget-start.json. This does not authorize purchases or resets.

Execution: three active worker slots beside the coordinator. Each pod has a builder
and a separate grader. Initial graders define the next useful acceptance test.
Builders then run one bounded milestone. Graders review the actual output before
another milestone is allowed. A grader may continue, redirect, or pause its pod.

A: a useful closed result with independent verification.
B: a verified nontrivial bridge or counterexample that removes a specific uncertainty.
C: a concrete, feasible next step, with evidence and an explicit test; allow one batch.
D: no new evidence, repeated failed approach, or work disconnected from the target;
   redirect once with a specific correction.
F: false premise, hidden assumption, or duplicate work with no useful difference;
   wrap the evidence and pause that approach.
These are progress judgments, not publication probabilities.

Each grade must name changed artifacts, the exact result, its assumptions, checks,
remaining gap, and the next falsifiable test. A paused pod records what would permit
restart. A negative result can earn A or B if it closes a relevant question.
No theorem-count, prose-volume or token-count proxy for progress.

All work stays in the source workspace until the coordinator imports it into the
isolated research-notebook Git worktree and pushes the existing draft PR. Builders
own only their assigned pod directory. Frozen prior evidence stays unchanged.
No external submission, author contact, paper acceptance or physics claim is implied.
