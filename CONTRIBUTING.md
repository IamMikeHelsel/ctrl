# Contributing to ctrl

Help make mathematical results useful and independently checkable. You can contribute a proof, a counterexample, a small integration, a benchmark, or a clearer explanation. A well-documented failure is valuable. You do not need to know Lean to contribute an engineering example.

## Pick a bounded contribution

| You can help with | A good first contribution | What we need to accept it |
|---|---|---|
| Using a result | One example in a familiar library or workflow | A minimal input, runnable command, expected output and one unsupported or rejected case |
| Testing an idea | One recorded trace, simulation or benchmark | Matched baseline, fixed settings, versions, full results including failures, and permission to redistribute inputs |
| Checking mathematics | A faithful formalization, missing proof bridge or counterexample | Exact statement, explicit assumptions, source attribution, kernel check and axiom audit |
| Improving language support | One Rust/Python capability with the same contract | Shared fixtures, boundary/error behavior, supported platforms and a maintainer |
| Improving explanations | A concrete benefit and integration example | Preserve assumptions and evidence limits; distinguish measured results from goals |

See the [research pipeline](https://iammikehelsel.github.io/ctrl/pipeline.html) for current questions. GO means worth a bounded next test, not a promised discovery or released feature. HOLD names a missing input; NO-GO closes a route, not necessarily the original question. Suggest another application domain or a counterexample even if you cannot implement it. If that page is not yet deployed, use [the source](site/pipeline.json).

For a larger change, start with an issue describing the user task, existing baseline, proposed contract and smallest discriminating test. Search existing issues first. Keep the first PR small enough to review and reproduce.

## Describe the claim before implementing it

Each contribution should say:

1. **Task:** who uses it, where it plugs in, and what they receive.
2. **Claim:** the precise property or measured improvement, with units and scope.
3. **Assumptions:** model, admissible inputs, numeric representation, timing and failure behavior.
4. **Evidence:** original source, exact revision, reproduction command, result and negative controls.
5. **Cost:** runtime, dependencies, integration changes, and maintenance obligations.
6. **Open boundary:** what is not established and the next useful test.

Use evidence-specific wording: *kernel-checked implication*, *exact finite certificate*, *numerical test*, *simulation*, or *physical measurement*. A theorem registry is provenance, not executable refinement. A successful solver run is a candidate until independently checked. A simulator result does not establish a physical robot guarantee. Avoid “production verified,” “safe,” “optimal” or “novel” without the precise scope and supporting evidence.

See [the novelty assessment](docs/assessments/2026-10-22-packaging/novelty-assessment.md) for examples of known methods, useful specializations and genuinely open targets.

For performance, name both baseline and denominator. Measure the whole user path, including representation construction, transfers and verification. Report absolute values and repeated-run variation. Do not add percentages from overlapping improvements. The notional bar is 30% for a major migration; smaller reproducible gains can justify a cheap optional adapter. A new supported capability may matter more than speed. These are prioritization guidelines, not fabricated results or rigid acceptance rules.

## Local verification

Read [AGENTS.md](AGENTS.md) and use the pinned toolchains. Do not change a toolchain merely to make a proof compile. Python commands use `uv`.

For the main Lean library:

```sh
scripts/check.sh ControlsLean/Area/YourFile.lean
scripts/check.sh
```

The full check builds the library and audits headline axioms. Add new headline results to `scripts/Audit.lean`. Explain changes to hypotheses explicitly; never weaken the intended statement silently. No escape hatches in accepted proof files. Follow the source-faithfulness rules in AGENTS.md and the relevant subproject.

For the separately packaged Erdős lab on main:

```sh
uv sync --frozen
uv run ruff check .
uv run ruff format --check .
uv run pytest -q
uv run erdos check --all
```

The research checkout uses a separate `ctrl` CLI and layout; commands are not interchangeable. Follow [the Erdős lab rules](docs/erdos-lab/rules.md). Approved Challenge statements stay frozen and solutions must bind to the exact statement. Never invent human approval. Missing human approval is not a passed gate.

For standalone tooling, run the tests named in its documentation and a meaningful failure case. For site changes, check local links, keyboard use, narrow-screen layout and any interactive calculations. Record the actual commands and outcomes, including unavailable tools and pre-existing failures. Do not edit unrelated work to make a suite green.

## Self-hosted CI and outside contributions

We use existing self-hosted runners. An outside PR does not grant permission to execute arbitrary code on a maintainer's machine. Follow [the runner verification policy](docs/SELF_HOSTED_VERIFICATION.md). Maintainers review code and workflow changes before importing a reviewed revision onto a trusted branch or manually checking it. Do not approve a fork workflow onto persistent runners, add `pull_request_target` checkout of fork code, or treat Docker alone as the isolation boundary.

A skipped or absent CI job is not verification. Record the tested SHA, commands, runner/target and outcomes. New commits invalidate earlier evidence for changed behavior. Public availability depends on the repository settings and runner isolation gates in the policy; a green workflow is not a public-release security review.

## AI assistance, sources and credit

AI-assisted contributions are welcome when the submitter understands and can explain the change. Disclose which parts were generated or assisted, what was checked, and what remains uncertain. Do not submit large unreviewed generated changes. Review capacity is a real project cost.

Credit the original theorem or algorithm separately from its formalization, implementation, benchmark and independent reproduction. Link primary sources and exact claims; do not claim discovery because Lean accepts a theorem. Include applicable licenses and notices for code, data, images and generated/adapted material. Do not copy source text or datasets without permission. Never include credentials, private customer traces or personal information in issues or fixtures.

## Review and merge

A merge means the scoped change is reviewed and its required checks pass; it does not turn a research lead into a production capability. Maintainers can merge a useful bounded contribution and improve organization, examples and prose later. Correctness, faithful claims, required checks and compatibility cannot be deferred to cosmetic cleanup.

The PR description should lead with the user-visible change, identify its evidence and limits, list the checks actually run, and name any follow-up owner. Use the [PR template](.github/pull_request_template.md). Reproducible negative results and clearly scoped research notes can be accepted without a positive performance outcome.
