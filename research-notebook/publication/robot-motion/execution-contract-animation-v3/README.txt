SAME GOAL, DIFFERENT MOTION — reviewed presentation repair candidate V3

Use MotionContractsV3. The source and data are from the frozen V2 artifact
b5a1f043f8814785069da6a7fe4cfe7970b7f16e4cede48554c971a2c676e759.
The prior folder and movie remain unchanged. Data.json is byte-identical.

Two repairs respond to independent animation review01:
1. The table names extra forward travel and defines it on-screen as the maximum
   beyond actual position at0.52s. This is not total path length.
2. The old legend and time readout are removed from their parent group after
   fading out, preventing their brief reappearance at the next group fade.
No numerical data, trajectory, metric or task decision changed.

The movie displays four actual simulated scalar positions for response100/s,
zero disturbance and the generous1.70s task. It interpolates saved0.5ms samples.
All metrics cover0.52–2.50s. The10mm cap applies only to the smooth reference.
The persistent footer states that calculation delay is omitted and no robot
was tested. This is an offline comparison, not an all-time numerical proof,
a real-time planner, a general VLA remedy, or a hardware demonstration.
The separate tighter task is not animated; only nativefast passes that task.

Render with the existing pinned Manim Community image, network disabled, using
manim -qm --fps24 --disable_caching scene.py MotionContractsV3 (separate --fps
and24 as shell arguments). FinalMP4 is copied outside media/ for repository sync.
No audio, external service or account-billed runner. No public release yet.
Independent review of these specific repairs is pending. Manim/3Blue1Brown
endorsement is not claimed.
