# Self-hosted verification and public contributions

The existing Mac and Spark runners are persistent machines. Treat any code executed on them as
trusted code with access to the runner account and its local environment. Read-only GitHub token
permissions, a Docker container, and a workflow `if` expression do not make arbitrary PR code safe.

## What runs automatically

The three check workflows run on pushes to `main` and `ci/trusted/**` in `IamMikeHelsel/ctrl`.
Only maintainers with repository write access should create a `ci/trusted/` branch, after reviewing
the complete candidate commit, including workflows, dependency changes, build hooks, Lean/Lake
configuration, scripts and Dockerfiles. The branch prefix is an explicit trust decision, not a
sandbox. A trusted branch can change its workflow; its authors are therefore trusted to run code.

There are no `pull_request`, `pull_request_target` or `workflow_run` triggers in these workflows.
A fork PR does not receive an automatic local check. Do not click **Approve and run** on a fork PR
workflow to obtain those checks. Review the contribution first and promote a trusted candidate
into the base repository. No PR checkout occurs under a privileged base-branch event.

Job identities remain `build`, `python`, `shell` and `check`. All routing is explicit:

- Lean and lint: `[self-hosted, ARM64, ctrl-local]` (either existing runner).
- Erdős lab: `[self-hosted, ARM64, ctrl-local, sparky]` (requires host Docker).
- Dependency updates: manual from `main`, using the same local label set.

No GitHub-hosted fallback, paid service or `RUNNER` variable override is used. Existing lint
advisories remain advisory: ruff lint and shellcheck have `continue-on-error: true`; formatting
is blocking. A successful lint workflow does not prove those advisory findings are absent.

## Required publication gate — not implemented by YAML alone

A fork can propose **new or changed workflow YAML**, including removal of these gates. Therefore
these file changes alone are not a sufficient security boundary for making the repository public.
GitHub specifically warns that malicious fork workflow code can run on self-hosted infrastructure
when approval is bypassed or granted.

Before public access, require approval for **all outside collaborators**, not just first-time
contributors, and verify that this policy actually applies to every fork workflow. Never approve
an untrusted fork run onto these persistent hosts; use the trusted-commit path below instead.
Where available, an administrator-enforced Actions event policy blocking PR execution, or runner
access restricted to selected protected-ref workflows, is a stronger boundary. Availability of
those features has not been established for this personal repository.

Do not leave a transition window in which public fork jobs can reach the hosts before policy is
verified. The fork-approval settings endpoint currently returns HTTP 422 because the repository
is private. This audit therefore **cannot certify the public fork policy**. If the policy cannot
be installed/verified before exposure, keep the repository private or disable Actions during an
explicitly authorized visibility transition, configure/verify the restriction, then re-enable.
No such settings, visibility or runner-service changes were made here.

Official references:

- [GitHub: managing Actions settings and fork approvals](https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/enabling-features-for-your-repository/managing-github-actions-settings-for-a-repository)
- [GitHub: secure use of Actions](https://docs.github.com/en/actions/reference/security/secure-use)

## Check a reviewed candidate

Prefer a maintainer-created `ci/trusted/<description>` branch containing the reviewed commit.
A push runs all three check workflows on that exact commit, including the complete Erdős gates;
path filters were removed so a candidate does not silently omit that gate. Any subsequent push
is a new trust decision. Compare the run's `headSha` with the intended commit before accepting it.
Do not check out or build the external PR on a persistent runner merely to inspect whether it is
safe. Review its source/diff first, including any newly added workflows.

For a one-off check, a maintainer can dispatch each existing check workflow **from `main`**:

```sh
# Replace this with the fully reviewed 40-character lowercase commit SHA.
reviewed_sha=<reviewed-commit-sha>
gh workflow run lean_action_ci.yml --repo IamMikeHelsel/ctrl --ref main \
  -f reviewed_sha="$reviewed_sha" -f trust_acknowledgement=TRUSTED_LOCAL_EXECUTION
gh workflow run lint.yml --repo IamMikeHelsel/ctrl --ref main \
  -f reviewed_sha="$reviewed_sha" -f trust_acknowledgement=TRUSTED_LOCAL_EXECUTION
gh workflow run erdos-lab.yml --repo IamMikeHelsel/ctrl --ref main \
  -f reviewed_sha="$reviewed_sha" -f trust_acknowledgement=TRUSTED_LOCAL_EXECUTION
```

The workflow definition is selected from `main`; the checked-out code is the explicit reviewed
SHA. Input is passed through an environment variable and validated before checkout, never inserted
into executable shell text. Checkout does not persist GitHub credentials. This acknowledgement
is a maintainer trust acknowledgement, not proof that the code is safe. Only dispatch code already trusted for
local execution. Full source review also covers external build inputs and mutable dependencies.

A dispatch run's GitHub event/check association is the workflow's `main` ref, not automatically the
candidate SHA. It is useful evidence with an explicit checkout SHA, but do **not** represent it as
an automatically satisfied required check on an external PR. Trusted-branch push runs are the
preferred SHA-associated path. Re-run the resulting integration commit before merging it when
changes to the base or cherry-picking produce different code.

No required status checks were configured in the inspected live ruleset. If maintainers add them,
keep the existing job names and establish a merge procedure for externally authored contributions;
a skipped PR check or a manual run on `main` is not a substitute for the candidate's checks.

## Docker boundary

`erdos-lab.yml` builds `docker/erdos-lab.Dockerfile` using the Spark host's Docker daemon. The
Dockerfile, build context, networked dependency retrieval and daemon are within the trusted build
boundary. The subsequent `docker run --network none` uses the image's non-root user, but neither
that nor deleting the image tag makes an untrusted Docker build safe or removes all host/cache
state. The runner account's Docker access is privileged. This workflow is for trusted code only.

## Live audit, 2026-10-22

Read-only API inspection found:

| Runner | State during inspection | Labels |
|---|---|---|
| `ctrl-local-mac-arm64` | online, idle | self-hosted, ARM64, ctrl-local, macOS, mac |
| `ctrl-local-sparky-arm64` | online, idle | self-hosted, ARM64, ctrl-local, Linux, sparky |

Repository Actions variables were empty. Actions were enabled, allowed actions were `all`, and
mandatory action SHA pinning was false. The active `minimal-main-protection` ruleset prevents
deletion and non-fast-forward pushes and requests Copilot review; it contained no required status
checks. The legacy branch-protection endpoint returned 404 (not protected by that mechanism).

Executed recent evidence, **before these changes**:

| Workflow / job | Commit | Actual runner | Result |
|---|---|---|---|
| [Lean Action CI / build](https://github.com/IamMikeHelsel/ctrl/actions/runs/39738529806) | `48a0a3a1269b738918d1ffb5a93b7f87fd4038bb` | Mac | success |
| [Lint / python and shell](https://github.com/IamMikeHelsel/ctrl/actions/runs/39738529770) | same `48a0a3a…` | Mac | success, advisory lint caveat above |
| [Erdős lab / check](https://github.com/IamMikeHelsel/ctrl/actions/runs/39738015728) | `84c3388bedcc8ae377b18080d6bf23e22733e85e` | Spark | success |

A separate Copilot code-review run failed; this is not one of these check jobs. No workflow was
dispatched during this audit. No new workflow success is claimed for the edited files.

Local validation of the edits:

- `actionlint` 1.7.7 passed on all four workflows, including installed shellcheck integration;
  only unknown custom-label diagnostics were suppressed after verifying those labels live.
- Parsed policy assertions checked trigger allowlists, four check-job routes, read-only token
  permissions, explicit-SHA checkout and disabled persisted credentials.
- 28 actual Bash input-validation cases across the four check jobs passed, including malformed
  SHAs, uppercase/non-SHA refs, a shell-substitution string and newline injection.
- Ten event-policy cases passed: trusted pushes/manual-main accepted; fork/PR/target/workflow-run,
  ordinary branch push and wrong/manual-unacknowledged refs rejected by the intended policy.
  This models the checked-in workflow; it does not claim fork YAML cannot be changed.
- `git diff --check -- .github/workflows docs/SELF_HOSTED_VERIFICATION.md` passed.
  A later whole-worktree check reported an unrelated concurrent `site/index.html` whitespace
  finding; the site owner was notified. No Lean/Docker rebuild was needed for these workflow-only
  edits; full edited-workflow execution remains pending a reviewed pushed ref.

To reproduce syntax validation with a temporary tool install:

```sh
GOBIN=/tmp/ctrl-workflow-audit-bin go install github.com/rhysd/actionlint/cmd/actionlint@v1.7.7
/tmp/ctrl-workflow-audit-bin/actionlint \
  -ignore 'label "(ctrl-local|sparky)" is unknown' .github/workflows/*.yml
git diff --check -- .github/workflows docs/SELF_HOSTED_VERIFICATION.md
```

Publication readiness remains conditional on the administrator-level public-fork gate above.

## Contribution/site follow-up validation

After adding the contribution pages, `uv run ruff check .` and
`uv run ruff format --check .` passed (20 Python files formatted), and `uv run pytest -q`
passed with **56 tests, one integration test deselected**. Twelve of these exercise the new
ControlsLean source guard: all five banned tokens, comments/strings, line positions, actual
source files, CLI failure, quote handling and an interpolation escape attempt.

Lean CI now explicitly runs `scripts/check.sh` after `lean-action`, with `setup-uv` available.
Upstream `lean-action` defaults its own axiom audit to false; the explicit repository script
is needed for the advertised source-policy and headline-axiom gate. The new standard-library
lexer masks nested comments and ordinary/raw strings, conservatively scans interpolation text,
and checks `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`. This is a lexical
guard, not a complete Lean parser or protection against arbitrary metaprogramming; kernel and
headline dependency checks remain separate. No existing proof source was changed.

`uv run erdos check --all` was attempted locally. The fresh worktree lacked `erdos/.lake`;
the first problem (261) began compiling Mathlib dependencies rather than using a populated
cache. After approximately six minutes, its owned process tree was conservatively terminated
to avoid duplicating the planned self-hosted build. **This local Erdős run is incomplete, not
passed or a proved source failure.** The exact trusted branch needs the full runner gate.

Static site checks passed: JavaScript syntax, local HTML links and unique IDs, 60 unique pipeline
records matching rendered decision/domain counts, seven calculator input cases plus submit
behavior, and all 24 decision/domain filter combinations. Counts are 55 GO, four NO-GO and
one HOLD; these are research decisions. Browser/layout testing is a separate owner’s check.
Five copied assessment links to absent campaign files were replaced with explicit research
provenance text; copied inventory/adoption notes now distinguish the research checkout from
this main-branch package.
