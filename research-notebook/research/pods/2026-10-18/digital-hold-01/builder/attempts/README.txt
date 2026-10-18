PRESERVED DEVELOPMENT ATTEMPTS
01: Initial Lean section variables were not explicitly included in theorem
    declarations. Source and exact failing build log are retained.
02: Working first implementation imported frozen RobustHold/ComparisonEnvelope.
    It was made self-contained over Mathlib for a smaller fresh proof closure.
03: Initial dispatch witness needed a derivative import, set-membership
    normalization and piecewise equality elaboration. Source/log retained.
04: The physical witness compiled; schedule numeric simplification still failed.
    Source/log retained. The final schedule proof uses explicit branch bounds.
05: A final redundant linarith after norm_num closed the positive-acceleration
    goal and caused 'No goals to be solved'. The exact failure log is retained.
pre-witness-verification: all proof and negative checks passed, but an intentional
    source edit during the run made source_unchanged false. This is not final
    verification evidence. The final verifier is rerun on the stable sources.
Negative contract mutations are kept separately under negative-controls/.
