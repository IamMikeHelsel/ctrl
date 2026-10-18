A tracking bound can support a task deadline

Open position-task.mp4 (26.17 s, 1280 by 720, 24 fps). The still PNG is the
closing scope card. review-midpoint.png, review-arrival.png and
review-deadline.png are inspected frames from the final video.

The blue curve is the reference q. The green band is the conditional proved
position bound q +/- 0.2 mm, drawn to scale. The moving dot belongs to q. No
physical trajectory x, simulation, measurement or robot motion is drawn.

The one scalar example has old goal 0 mm and new authoritative goal 20 mm.
The task starts at absolute time 0.20 s; reference execution starts at 0.22 s.
The four-box width is 0.20 s. At 0.62 s, q is exactly 10 mm and the theorem
places x between 9.8 and 10.2 mm. Thus progress measured from the old goal is
at least 9.8 mm. This is not a claim about displacement from an exactly zero
physical initial position. At 1.02 s, q reaches 20 mm. The theorem keeps x
within 0.2 mm of that goal through 2.00 s. The 1.50 s position deadline passes.
The 0.62 s arrival deadline fails: at least 9.8 mm of goal error remains then.

These claims require TaskFixtures.FixedPlant: the stated continuous-state
feedback controller and scalar uncertain-lag ODE; response rate in [80,120]/s;
disturbance magnitude at most 0.01 m/s^2; and the initial transformed-error cube
  forall i, |coordinates 0 (scaledError 10 f stepReference 0) i| <= 1/5000.
This cube is stronger than an initial position band alone. There is one fixed
reference event and no later revision through the horizon. The theorem does
not supply the benchmark's physical speed/acceleration rest tolerances, a
digital implementation guarantee, or a robot guarantee. The moving-goal-08
reversal comparison is separate numerical evidence and is not proved here.

Source claims: TaskFixtures.twenty_mm_progress, twenty_mm_arrival,
twenty_mm_deadline, halfway_deadline_impossible, and actual_rest_not_supplied.
controls_direct_independent_review explicitly accepted the claim-level scope
before rendering. display-check.json binds the source and independent proof
review. check_display.py checks plotted endpoint values with Python Fraction;
that display check is not a new Lean proof. No proof source was changed.

Reproduce in a new writable copy: sh render.sh
The script uses the already present pinned Manim Community Docker image with
--pull never and --network none. It installs nothing. The workspace's
.tools/manim-python environment could not import manim, so the same local
Docker pin as prior workspace animations was used. FFmpeg extracts the still.
media/ is temporary render output and is excluded from the final manifest.

Mike Helsel requested the task framing and explanations of completed ideas.
No publication novelty claim, hardware run, paper edit, or Git operation is
part of this visual task. Root handles notebook and repository integration.
