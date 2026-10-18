Steady enough to move

steady-enough.mp4 is a silent Manim Community explanation of target selection.
It runs for 23.416667 seconds at 1280 x 720 and 24 frames per second.

The fixed-target example uses an anchor of 0 mm, a true target of 0 mm, proposal
errors bounded by 0.5 mm, and a strict 2 mm acceptance threshold. The proposed
targets vary, but the retained target stays at 0 mm. The anchor is itself valid.

The next example changes the intended target to 20 mm. A valid proposal of
19.8 mm passes the target gate. The animation changes a decision card; it does
not depict an instantaneous robot move. A downstream motion-admission check
can still reject the requested path.

The separate 1 mm example starts again from a 0 mm anchor. A valid proposal of
1.3 mm does not exceed the 2 mm threshold. The gate therefore keeps 0 mm. This
shows the cost in target resolution, including for a deliberate small move.

The closing schematic separates target selection, smooth feasible motion,
and physical tracking with a stopping reserve. The checked scope is the
target gate and its fixed-hold composition. The complete chain for moving
targets and contact remains open. These bounds do not establish zero physical
vibration or a model of human neural control.

Every scene is labelled:
  Target selection only • not a robot simulation

Mathematical sources:
  ../CommitmentGate.lean
  ../QuietHold.lean
Verification record:
  ../verification.json

Reproduce from the workspace root:
  research/adjacent-controls/steady-motion/animation/render.sh

The script uses the existing pinned Manim Community Docker image, with
network access disabled. It installs no software. The Lean sources are not
changed by this animation. See render-manifest.json for exact hashes.

Frames extracted with local ffmpeg and inspected after the final render:
  jitter-frame.png       7 seconds
  change-frame.png      11 seconds
  resolution-frame.png  16 seconds
  scope-frame.png       22 seconds

The labels, units, threshold signs and scope statement are readable in all
four frames. No clipped text or overlapping graph labels were found.

ffprobe confirmed one H.264 video stream at the stated resolution and frame
rate, with no audio stream. video-metadata.json preserves its output.
