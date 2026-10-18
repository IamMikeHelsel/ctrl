Think often. Switch smoothly.

smooth-replanning.mp4 is a silent, 26.5-second Manim Community explanation.
It renders at 1280 x 720 and 24 frames per second.

The first graph contrasts a matching acceleration join with an acceleration
reset after the same 20 ms wait. Each open segment has jerk magnitude 10 m/s³.
The reset at the join still prevents a finite global jerk bound. The graph is
an analytic command illustration, not a VLA rollout or physical measurement.

The second scene uses the exact examples from SmoothReplan.lean. Starting from
q=0 m, v=0.1 m/s and a=0 m/s², the 20 ms constant-jerk candidate with j=10 has
endpoint 2.013333... mm and passes the finite admission checks. A 2.5 mm endpoint
requires j=375 for this construction and is rejected under the same limits.

The final scene states the proof scope. Histories are finite. Actual tracking,
contact and task progress remain separate. Bounded jerk can still allow dithering.
No new control method, hardware validation or human-like behavior is claimed.

Reproduce from the workspace root:

  research/adjacent-controls/vla-smooth-replanning/animation/render.sh

The script uses the existing pinned Manim Community Docker image with network
access disabled. It installs no software. See render-manifest.json for hashes.
The Lean source is unchanged by this animation work.

Inspected frames:
- switch-frame.png at 11 s: graph, units, switch and jump labels.
- admission-frame.png at 17 s: unchanged limits and accepted/rejected candidates.
- proof-frame.png at 25 s: result and limits.
All three frames were inspected after the final render. Labels are readable,
inside the frame and do not cover the curves or numbers they explain.
