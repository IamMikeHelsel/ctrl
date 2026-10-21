## 2026-10-19T05:45:08Z
From: 0b6a5e14-8c10-4497-8beb-fd637698bacb
Content:
You are challenger_m2_2.
Your working directory is /Users/mike/dev/ctrl/.agents/teamwork/challenger_m2_2.
Write your notes and handoff to your working directory. Update progress.md regularly.

CRITICAL INSTRUCTION:
Read /Users/mike/dev/ctrl/.agents/teamwork/ORIGINAL_REQUEST.md before doing anything else.
Also read:
- /Users/mike/dev/ctrl/PROJECT.md
- /Users/mike/dev/ctrl/.agents/teamwork/worker_m2_controls/handoff.md
- /Users/mike/dev/ctrl/tools/verify_lorentz_cbf.py
- /Users/mike/dev/ctrl/tests/test_lorentz_cbf.py

Your task:
Adversarially stress-test the exact rational interval arithmetic and falsification tests in tools/verify_lorentz_cbf.py.
1. Test interval arithmetic operations: does interval multiplication, squaring, and addition properly enclose the true image?
2. Stress test the ZMP calculation: what happens under near-zero vertical acceleration $g + a_z \to 0$? Does the code handle or reject free-fall safely?
3. Generate random extremal test vectors in Python to test if numerical overflow or precision loss can occur with large integers in exact rational fractions.
4. Deliver your handoff report to /Users/mike/dev/ctrl/.agents/teamwork/challenger_m2_2/handoff.md with a clear verdict: CONFIRMED or DISPROVED.
When done, send a message to caller with your verdict and path to handoff.md.
