## 2026-10-19T06:55:14Z
# Task Assignment: Byers-Nash mf13 Deep Explorer

## Objective
Deeply investigate `work/pod/mf13` (Byers–Nash conjecture on real 6x6 matrices).
Authoritative sources to read:
- `/Users/mike/dev/ctrl/.agents/teamwork/ORIGINAL_REQUEST.md`
- `/Users/mike/dev/ctrl/work/pod/mf13/FINDINGS.md`
- `/Users/mike/dev/ctrl/work/pod/mf13/PRIOR_ART.md`
- Code and notes in `/Users/mike/dev/ctrl/work/pod/mf13/` (including `opt/`, `lean/`, and any verification scripts).

Specific investigation points:
1. Mathematical structure:
   - What is the Byers–Nash conjecture for $n=6$?
   - How is it reduced to an 11-parameter convex family?
   - What are the numerics indicating $k(A) - s(A) \le 0$? What are the equality sets?
2. The Lean gap:
   - What is the exact normal-form lemma for rank ≤ 4 real skew 6×6 matrices?
   - What is the status of Lean formalization in `work/pod/mf13/lean/`? What theorems exist, what is `sorry`'d, and what is missing?
3. The rational SDP / SOS certificate pathway:
   - How can `tools/sdp_rational_cert.py` or polynomial SOS be applied to certify $k(A) \le s(A)$ on the reduced family?
   - How should the equality sets be handled in an exact certificate?
4. Concrete attack plan:
   - Provide step-by-step blueprint for a Worker to formalize the rank ≤ 4 normal-form lemma in Lean or build the exact certificate.

Deliver your complete findings in `/Users/mike/dev/ctrl/.agents/teamwork/explorer_mf13_1/handoff.md`.
