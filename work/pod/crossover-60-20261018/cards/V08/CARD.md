# V08: Minimal relative pose and degeneracy

**NOT REVIEWED — inventory card only.**

Question: Can a five-correspondence calibrated relative-pose solve distinguish isolated real solutions from degenerate solution families with a checkable certificate?

Prior work (catalogued): Five-point relative pose is named in the survey; epipolar forward identity exists locally.

Obstacle: Need actual elimination equations and saturation conditions; quotient-ring dimension and generic root count are not guarantees for every instance.

Candidate crossover: Use rank stratification and control observability analysis before algebraic solving.

Proposed cheap test: Compare a generic five-ray fixture with planar/pure-rotation fixtures; test rank and substitution residuals of all claimed candidates.

Selection reason: Distinct vision question with source-linked obstacle and small test; balanced-domain selection. Subjective rubric, not success probability.

Sources:

- /Users/mike/Dev/ctrl/.agents/teamwork/explorer_survey_vision_1/handoff.md
- /Users/mike/Dev/ctrl-research-notebook/ControlsLean/Vision/Epipolar.lean
