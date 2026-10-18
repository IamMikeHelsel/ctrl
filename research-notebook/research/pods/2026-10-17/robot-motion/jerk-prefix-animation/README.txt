Alternating jerk can still build speed

Open jerk-prefix.mp4 for the animation. jerk-prefix-still.png is its final frame.
The four aligned plots show reference jerk, acceleration, velocity and position.
The vertical marker shows the same elapsed time in each plot. Playback is slowed
for explanation; 12 seconds of marker motion represents 120 ms of reference time.

Public caption
--------------
Jerk is the rate of change of acceleration. In this fixed reference trace, jerk
alternates between +7.5 and -7.5 m/s³ every 20 ms. Acceleration rises from zero
to +0.15 m/s², then returns to zero. It does not become negative. Velocity thus
accumulates. After three pairs, the reference has moved 0.54 mm and still has
velocity 9 mm/s. Zero acceleration at that instant does not mean the motion has
stopped. Bounded jerk alone does not keep a stationary task still.

Scope
-----
This is an exact ideal polynomial explanation of the first six executed
intervals in the fixed hold-jitter comparison. Execution begins at absolute
time 0.22 s. The displayed elapsed interval 0 to 120 ms therefore ends at 0.34 s.
The initial reference position, velocity and acceleration are all zero.

q is the reference position. The animation does not show physical position x,
a simulated physical axis, sensor data, or a hardware measurement. It explains
one finite trace. It does not say that Ruckig ignores time, is defective, or that
every Ruckig plan or replanning policy behaves this way. Later replans in this
same comparison change the pattern. A planned braking segment can also make
acceleration negative; that is outside the six intervals shown here.

The independent review checks exact rational ideal prefix endpoints and compares
them with fresh native Ruckig states. All six states agree within 1e-14 in each
SI component. This is not exact floating-runtime equivalence. Across the full
comparison, native double clocks and canonical rational switch times can select
different jerk branches within about 1.288e-16 s of a switch. Small native phase
durations and state roundoff remain in the comparison evidence. This animation
does not draw those sub-picosecond distinctions. At each displayed switch, q,
v and a are continuous, while jerk can jump. The moving jerk dot uses the new
segment at internal switches and the last segment's left value at the end.

Evidence and method
-------------------
Input report: ../comparison-04/grader/review-report.txt
Input data:   ../comparison-04/grader/trace-diagnosis.json
exact_check.py independently integrates each constant-jerk segment with Python
Fraction arithmetic. It checks the six endpoint values and times against the
review. It records their source hashes in exact-check.json. This check is exact
arithmetic, not a Lean proof.

For each segment of length h and jerk j, the integration is:
  q_new = q + v*h + a*h²/2 + j*h³/6
  v_new = v + a*h + j*h²/2
  a_new = a + j*h

The exact final SI values are q=27/50000 m, v=9/1000 m/s and a=0 m/s².
Acceleration is affine on each interval. Its endpoint values are 0 and 3/20,
so it stays nonnegative throughout this ideal prefix.

Reproduce
---------
Run: sh render.sh
The script checks the existing pinned Manim Community Docker image before use.
It uses --pull never and --network none. It installs nothing. It renders at
1280×720 and 24 fps, then extracts a PNG still with the local FFmpeg executable.
The same image pin is used by tracking-replans/animation/render.sh.

Source: prefix.py. Exact check: exact_check.py. Output hashes: output-hashes.json.
The media/ folder contains render intermediates. jerk-prefix.mp4 and the PNG
are the final outputs to preserve. No frozen proof or comparison file was edited.
No Git commit, push, or merge was made by this visual task.
