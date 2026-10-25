# Task Assignment: Byers-Nash mf13 Rational Certificate Worker

## Objective
Implement an exact rational semidefinite / algebraic certificate tool for real 6x6 Byers-Nash pairs, establishing exact rational certificates that $s(A) \ge k(A)$ on the active mf13 lane.

## Working Directory
`/Users/mike/dev/ctrl/.agents/teamwork/worker_mf13_cert`

## Mandatory Integrity Warning
DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_preview_auditor will independently verify your work.

## Detailed Scope
1. Exclusive write ownership:
   - `/Users/mike/dev/ctrl/tools/certify_mf13_pair.py`
   - `/Users/mike/dev/ctrl/tests/test_mf13_rational_cert.py`
2. Technical Implementation:
   Follow the Track B blueprint from `/Users/mike/dev/ctrl/.agents/teamwork/explorer_mf13_1/handoff.md` Section 5:
   - Adapt `tools/sdp_rational_cert.py` to handle $6 \times 6$ Byers-Nash pairs:
     (a) For given rational skew pair $(K, Y) \in \mathbb{Q}^{6 \times 6}$ with trace moments $m_0 = m_1 = m_2 = 0$, compute rational basis of $\ker(\Phi_{K,Y})$ and particular solution $H_0$.
     (b) Set up the dual SDP for $\min_z \|B_S(z)\|_2 \ge 1$ over the 9D affine family $A(z)$.
     (c) Solve numerically, project into $\mathbb{Q}^{21 \times 21}$ satisfying the affine constraints, and compute exact rational $LDL^\top \succ 0$ factorization verifying that all pivots $D_i > 0$.
     (d) Implement the Common-T Involution Certifier for the 8D equality locus: given $(K, Y)$, solve for the exact rational involution $T \in \mathbb{Q}^{6 \times 6}$ ($T=T^\top, T^2=I, TK=-KT, TY=-YT$) and verify the exact pairing $\langle YT, \mathcal{L}_A(KT) \rangle = \|Y\|^2$, proving $s(A) \ge 1$ identically on this locus!
   - Test instances:
     * Card M05 candidate pairs ($t=1/2, t=1/3$).
     * Calibration pair $K = Y = \operatorname{diag}(J, 2J, 3J)$ at $A = \frac{1}{2}I_6$.
     * Common-T involution candidates.
3. Tests & Regression:
   - Implement comprehensive tests in `tests/test_mf13_rational_cert.py`.
   - Run `uv run python tools/certify_mf13_pair.py`.
   - Run `uv run pytest -v tests/test_mf13_rational_cert.py`.
   - Run `uv run ruff check tools/certify_mf13_pair.py tests/test_mf13_rational_cert.py`.
   - Run full regression `uv run pytest -q`.
4. Deliver your complete report to `/Users/mike/dev/ctrl/.agents/teamwork/worker_mf13_cert/handoff.md`.
When done, notify caller via `send_message`.

## 2026-10-19T07:07:42Z
[Message] timestamp=2026-10-19T07:07:42Z sender=0b6a5e14-8c10-4497-8beb-fd637698bacb priority=MESSAGE_PRIORITY_HIGH content=Read /Users/mike/dev/ctrl/.agents/teamwork/ORIGINAL_REQUEST.md and /Users/mike/dev/ctrl/.agents/teamwork/worker_mf13_cert/DISPATCH.md.
Your working directory is /Users/mike/dev/ctrl/.agents/teamwork/worker_mf13_cert.
Write only to your working directory. Update progress.md regularly with timestamped progress.

MANDATORY INTEGRITY WARNING:
DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_preview_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.

Your assigned scope:
Implement exact rational semidefinite / algebraic certificate tools for real 6x6 Byers-Nash pairs on the active mf13 lane.
1. Exclusive write ownership:
   - /Users/mike/dev/ctrl/tools/certify_mf13_pair.py
   - /Users/mike/dev/ctrl/tests/test_mf13_rational_cert.py
2. Follow the Track B blueprint from /Users/mike/dev/ctrl/.agents/teamwork/explorer_mf13_1/handoff.md Section 5:
   - Adapt tools/sdp_rational_cert.py for 6x6 Byers-Nash pairs:
     (a) Compute rational basis of ker(Phi_{K,Y}) and particular solution H0 for rational pairs with m0=m1=m2=0.
     (b) Set up dual SDP for min_z ||B_S(z)||_2 >= 1 over the 9D affine family A(z).
     (c) Project numerical dual solution to Q^{21x21} and compute exact rational LDL^T > 0 factorization with all D_i > 0.
     (d) Common-T Involution Certifier: for the 8D equality locus, compute rational involution T (T^T=T, T^2=I, TK=-KT, TY=-YT) and verify <YT, L_A(KT)> = ||Y||^2, certifying s(A) >= 1 identically!
   - Test instances: Card M05 candidate pairs (t=1/2, t=1/3), calibration pair diag(J, 2J, 3J) at A = (1/2)I_6, and common-T involution candidates.
3. Verification:
   - uv run python tools/certify_mf13_pair.py
   - uv run pytest -v tests/test_mf13_rational_cert.py
   - uv run ruff check tools/certify_mf13_pair.py tests/test_mf13_rational_cert.py
   - uv run pytest -q (zero regressions)
4. Deliver your complete report to /Users/mike/dev/ctrl/.agents/teamwork/worker_mf13_cert/handoff.md.
When complete, notify caller via send_message.

## 2026-10-19T07:11:20Z
[Message] timestamp=2026-10-19T07:11:20Z sender=0b6a5e14-8c10-4497-8beb-fd637698bacb priority=MESSAGE_PRIORITY_HIGH content=**Context**: Critical guidance on Byers-Nash mf13 exact certificates and equality sets.
**Content**:
Parent directive regarding mf13 certification:
Watch the equality sets ($k=s$ on the rank-4 ridge and at $K=Y=\operatorname{diag}(J, 2J, 3J)$). A strict SDP certificate ($S \succ 0$ with positive slack) cannot exist there because the margin is exactly 0.
The certificate at/near these sets must be non-strict / exact-SOS (such as the exact algebraic Common-T involution pairing $\langle YT, \mathcal{L}_A(KT) \rangle = \|Y\|^2$, which identically proves $s(A) \ge k(A)$ without needing an interior SDP slack), or the interior SDP domain must exclude neighbourhoods of the equality sets with a separate argument.
Ensure the Hypothesis Audit is completely respected (no hidden slack or assumed margins).
**Action**: Incorporate this exact-SOS / non-strict algebraic certificate design in `tools/certify_mf13_pair.py`.


