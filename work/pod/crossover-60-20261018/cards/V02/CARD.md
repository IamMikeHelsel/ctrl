# V02: Homography pose ambiguity and cheirality

**NOT REVIEWED — inventory card only.**

Question: Given a calibrated plane-induced homography, which rigid pose and plane candidates satisfy reconstruction and positive-depth constraints, including degeneracies?

Prior work (surveyed): Survey proposes analytical decomposition; existing Lean file only proves forward identities.

Obstacle: Survey fixed eight-to-two multiplicity and novelty claims are not established; pure rotation, scale conventions and visible points can change ambiguity.

Candidate crossover: Treat branches as finite certificates like SAT witnesses instead of assuming a solution count.

Proposed cheap test: For identity, pure translation and generic rotation homographies, test candidate reconstruction and signed depths; report sets rather than fixed count.

Selection reason: Distinct vision question with source-linked obstacle and small test; balanced-domain selection. Subjective rubric, not success probability.

Sources:

- /Users/mike/Dev/ctrl/.agents/teamwork/explorer_survey_vision_1/handoff.md
- /Users/mike/Dev/ctrl-research-notebook/ControlsLean/Vision/Homography.lean
