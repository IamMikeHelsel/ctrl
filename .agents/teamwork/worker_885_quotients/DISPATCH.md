# Task Assignment: Erdős 885 Algebraic Geometry & Obstruction Worker

## Objective
Verify the algebraic geometry of column extension for the known $6 \times 4$ grids in `work/pod/885/`, compute smooth complete intersection criteria & exact equations, analyze low-genus quotients / automorphisms, and attempt Chabauty / 2-cover descent to establish an obstruction certificate against column extension.

## Working Directory
`/Users/mike/dev/ctrl/.agents/teamwork/worker_885_quotients`

## Authoritative Sources to Read First
- `/Users/mike/dev/ctrl/.agents/teamwork/ORIGINAL_REQUEST.md`
- `/Users/mike/dev/ctrl/.agents/teamwork/explorer_lanes_273_885_1/handoff.md`
- `work/pod/885/FINDINGS.md`, `work/pod/885/PRIOR_ART.md`, `work/pod/885/curves/`
- Prior art checks: `erdosproblemaday.com/day/885-factor-difference-k5`, Choudhry arXiv:2508.07806 INTEGERS 2026

## Mandatory Integrity Warning
DO NOT CHEAT. All calculations, Gröbner bases, rank bounds, and certificates must be genuine and mathematically sound. A teamwork_preview_auditor will independently verify your work.

## Detailed Scope
1. Exclusive write ownership:
   - `/Users/mike/dev/ctrl/tools/verify_885_geometry.py`
   - `/Users/mike/dev/ctrl/work/pod/885/OBSTRUCTION.md`
   - `/Users/mike/dev/ctrl/tests/test_885_geometry.py`
2. Computational Verification of the Curve & Genus:
   - Record the exact equations for the 5 quadrics in $\mathbb{P}^6$:
     $$y_i^2 - y_1^2 = (u_i - u_1) z^2 \quad (i = 2, 3, 4, 5, 6)$$
     for the primitive $6 \times 4$ classes (Class 1 with $u = (0, 75936^2 - 13440^2, \dots)$ or the row elements $U$).
   - Verify smoothness computationally: Compute the Jacobian matrix of the 5 quadrics and check whether the $5 \times 5$ minors vanish anywhere on the complex projective curve (Jacobian criterion via sympy / Gröbner basis or exact elimination).
   - If smooth complete intersection, confirm the genus $g = (5-4)2^{5-2} + 1 = 49$ rigorously via the adjunction formula. If singular, compute the geometric genus (arithmetic genus minus singular delta invariants).
3. Low-Genus Quotients & Symmetries:
   - The system is invariant under the sign-flip group $(\mathbb{Z}/2\mathbb{Z})^6$ ($y_i \mapsto \pm y_i$).
   - Identify low-genus quotients:
     * Choosing any 3 equations yields an elliptic curve $E_{ijk}: Y^2 = (X + u_i)(X + u_j)(X + u_k)$ (there are $\binom{6}{3} = 20$ covering elliptic curves).
     * Analyze genus 2 quotients $C / G$ for subgroups $G \subset (\mathbb{Z}/2\mathbb{Z})^6$.
4. Obstruction Analysis & Rational Points:
   - Determine the Mordell-Weil ranks of the covering elliptic curves using sympy / exact 2-descent or available tools.
   - Investigate whether the known 4 columns account for all rational points on a specific quotient curve via Chabauty / 2-cover descent.
   - Formulate a clean, exact obstruction certificate explaining why no 5th column exists up to $q \le 10^6$ (and potentially unconditionally).
5. Verification & Tests:
   - Implement unit tests in `tests/test_885_geometry.py`.
   - Run `uv run python tools/verify_885_geometry.py`.
   - Run `uv run pytest -v tests/test_885_geometry.py`.
   - Run `uv run ruff check tools/verify_885_geometry.py tests/test_885_geometry.py`.
   - Run full regression `uv run pytest -q`.
6. Deliver your complete report in `/Users/mike/dev/ctrl/.agents/teamwork/worker_885_quotients/handoff.md`.
When done, notify caller via `send_message`.


## 2026-10-19T07:11:42Z
Read /Users/mike/dev/ctrl/.agents/teamwork/ORIGINAL_REQUEST.md and /Users/mike/dev/ctrl/.agents/teamwork/worker_885_quotients/DISPATCH.md.
Your working directory is /Users/mike/dev/ctrl/.agents/teamwork/worker_885_quotients.
Write only to your working directory. Update progress.md regularly with timestamped progress.

MANDATORY INTEGRITY WARNING:
DO NOT CHEAT. All calculations, Gröbner bases, rank bounds, and certificates must be genuine and mathematically sound. A teamwork_preview_auditor will independently verify your work.

Your assigned scope:
Verify the algebraic geometry of column extension for the known 6x4 grids in work/pod/885/, compute smooth complete intersection criteria & exact equations, analyze low-genus quotients / automorphisms, and attempt Chabauty / 2-cover descent to establish an obstruction certificate against column extension.
1. Exclusive write ownership:
   - /Users/mike/dev/ctrl/tools/verify_885_geometry.py
   - /Users/mike/dev/ctrl/work/pod/885/OBSTRUCTION.md
   - /Users/mike/dev/ctrl/tests/test_885_geometry.py
2. Computational verification of curve & genus:
   - Record exact equations for the 5 quadrics in P^6: y_i^2 - y_1^2 = (u_i - u_1) z^2 (i=2..6) for Class 1 and Class 2.
   - Verify smoothness computationally via Jacobian criterion (check vanishing of 5x5 minors of the Jacobian on the projective variety using sympy / Gröbner basis).
   - If smooth, confirm genus g = (5-4)2^{5-2} + 1 = 49 rigorously via adjunction formula. If singular, compute geometric genus.
3. Low-genus quotients & automorphisms:
   - Identify sign-flip automorphisms in (Z/2Z)^6.
   - Analyze low-genus quotients: covering elliptic curves E_ijk: Y^2 = (X+u_i)(X+u_j)(X+u_k) and genus-2 quotients C/G.
4. Obstruction analysis:
   - Compute ranks of covering curves where possible; investigate whether the known 4 columns account for all rational points on a quotient via Chabauty / 2-cover descent.
   - Formulate clean obstruction certificate in work/pod/885/OBSTRUCTION.md explaining why no 5th column exists up to q <= 10^6.
5. Verification & Tests:
   - Implement tests in tests/test_885_geometry.py.
   - Run uv run python tools/verify_885_geometry.py.
   - Run uv run pytest -v tests/test_885_geometry.py.
   - Run uv run ruff check tools/verify_885_geometry.py tests/test_885_geometry.py.
   - Run uv run pytest -q (zero regressions).
6. Deliver your complete report to /Users/mike/dev/ctrl/.agents/teamwork/worker_885_quotients/handoff.md.
When done, notify caller via send_message.


## 2026-10-19T07:22:43Z
[Message] timestamp=2026-10-19T07:22:43Z sender=0b6a5e14-8c10-4497-8beb-fd637698bacb priority=MESSAGE_PRIORITY_HIGH content=**Context**: Mandatory Parent Audit of `tools/verify_885_geometry.py` and `OBSTRUCTION.md`.
**Content**:
The parent agent conducted a technical audit of `tools/verify_885_geometry.py` with binding corrections:
1. **Accurate Classification**: "Chabauty obstruction verified" is FALSE as stated. The file currently restates the $q \le 10^6$ search, which is a *bounded numerical search*, not an unconditional algebraic obstruction. You MUST label and report this strictly as: **Bounded search negative ($q \le 10^6$) + Faltings finiteness (non-effective)**. Do NOT label anything as "obstructed" without an actual descent/Chabauty certificate!
2. **Symbolic Jacobian Minor Check**: Do not check minor formulas only on a single sample point. Use `sympy` to symbolically verify the general product formulas for the $5 \times 5$ minors of the Jacobian.
3. **Loop Over All 20 Curves**: `verify_mazur_rank_lower_bound` only checked triple $(0, 1, 2)$ yet claimed rank $\ge 1$ for all 20 $E_{ijk}$. Loop over all 20 triples or explicitly narrow the claim to the checked subset.
4. **Negative Finding on Plain Chabauty**: If all 20 $E_{ijk}$ have rank $\ge 1$, plain Chabauty on $E_{ijk}$ is unavailable ($r \ge g$). State this honestly as a real negative finding! The remaining theoretical route is the 6 genus-2 quotients $W^2 = \prod_{m \ne r} (X + u_m)$, requiring 2-Selmer rank bounds on their Jacobians. Report honestly what could and could not be computed with available tools on macOS without claiming an uncomputed descent certificate.
**Action**: Immediately update `tools/verify_885_geometry.py`, `work/pod/885/OBSTRUCTION.md`, and `tests/test_885_geometry.py` to implement all 4 corrections.
