SAME GOAL, DIFFERENT MOTION — explanatory Manim animation
Integration artifact; independent presentation review pending.

The movie animates actual simulated position from four independently reviewed
traces for one scalar plant: response100/s, disturbance0, generous deadline1.70s.
It interpolates saved samples for display. It is not a hardware recording or
an all-time numerical proof. Planning time is omitted, as the persistent footer
states. The new smooth plan has a reference-only10mm forward cap; actual travel
has a separate measured value. No general VLA or optimal-planning claim is made.

The first scene shows the same moving start and the return request at.52s.
The second compares squared-jerk integral, extra forward travel and peak jerk
over[.52,2.50]s. Values are for the displayed plant, not all-plant ranges.
The last scene separates task, reference and actual-motion contracts.
All four pass this generous task. The separate tight-task experiment must not
be inferred from these generous-task curves: only native fast passes it, while
the FIR selector rejects the tight return request.

Reproduction
Run prepare.py with Python3 from this workspace. It validates the frozen input
manifests and copies values into data.json. scene.py consumes only that JSON.
Render with the existing pinned Manim Community Docker image recorded in
render-environment.json, with network disabled. No package installation or
account-billed runner is required. The final MP4 is copied out of media/ because
the repository sync excludes generated Manim intermediates.

Before public use
Review the video and exact metric labels independently, keep the offline/model
limits and author disclosure, and obtain Mike's release/license decision.
The movie does not claim that Manim or3Blue1Brown endorses this work.
