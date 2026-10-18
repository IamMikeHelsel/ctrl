RECOVER FIRST. THEN STAY SAFE.
Manim Community explanatory animation — 2026-10-17

Open recovery-proof.mp4 (34 seconds; silent; H.264, 1280x720, 24fps).
Source: recovery.py. No LaTeX, audio, external artwork or paid services.
Manim Community v0.22.0, not Grant Sanderson's separate ManimGL distribution.

What it communicates
--------------------
A state outside the previously certified ellipsoid first receives a fixed
negative command. At normalized time 1.25, it enters the ellipsoid and hands off
to the sampled controller without a reset. All state coordinates are continuous.
The terminal velocity and acceleration are explicitly nonzero; this is entry
into a safe region, not arrival at rest.

The moving trace is ONE illustrative trajectory:
  z0=(1, 0.5, 0), fixed r=1, held backup u=-1 for T=1.25;
  then h=0.1, u_n=clip_1(-x_n-3v_n-2a_n), with zero errors.
The exact analytic held-flow formula is evaluated in ordinary floating point
for drawing. No numerical trace or sampled maximum is used as a proof.
The certificate energy uses the same P as the checked Lean model:
  [[38/5, 257/25, 5], [257/25, 1319/50, 769/50], [5, 769/50, 278/25]].
State dynamics: x'=v, v'=a, a'=r(u-a). Time and states are normalized.

The final card states the separate universal checked result:
  every initial state x in [.99,1.01], v in [.49,.51], a in [-.01,.01];
  every fixed r in [.9,1.1]; exact, zero-error backup u=-1 until T=1.25;
  after handoff, 0<hmin<=h_n<=.2 and |e_n|+|d_n|<=1/90;
  own sampled feedback clip_1(input+e_n)+d_n, both errors held inside the lag;
  every continuous actual ODE execution has |x(t)|<=2 for every t>=0.
This is not a claim of hardware conformance, optimal recovery, controller
superiority, zero terminal velocity or robustness to backup disturbance.
The displayed box is a list of parameter intervals, not a geometric projection.

Proof provenance
----------------
The source proof artifacts are in ../recovery-proof/, especially:
  RecoveryPath.lean: entire backup path; initial box outside old ellipsoid.
  TerminalBase.lean and TerminalCells.lean: exact terminal certificate.
  RecoveryHandoff.lean: actual ODE execution, continuous handoff, uniqueness.
  RecoveryBox.lean: all-time concrete recovery result and safe existence.
  PhysicalRecoveryBox.lean: physical-coordinate result (not depicted here).
render-manifest.json hashes the relevant source snapshots and output.
No proof sources were modified for this animation. The animation is explanatory
material; Lean compilation and kernel replay are recorded separately.

Render locally with the official image
-------------------------------------
From this animation directory:
  docker run --rm --network none -v "$PWD:/manim" \
    manimcommunity/manim:v0.22.0 \
    manim --resolution 1280,720 --fps 24 --disable_caching \
      recovery.py RecoveryProof -o recovery-proof.mp4

The generated file is media/videos/recovery/720p24/recovery-proof.mp4.
The top-level recovery-proof.mp4 is a copy for convenient playback.
To refresh the illustrative numeric summary:
  docker run --rm --network none -v "$PWD:/manim" \
    manimcommunity/manim:v0.22.0 python recovery.py

Reproducible image used:
  manimcommunity/manim@sha256:3c3ce944c09d6fa73de59fe1e7a95e334e193ae9c2275d65937054e675f87b03
The pulled image is arm64. See image-provenance.txt and render.log.
The Text font is Noto Sans, available in that image.

Setup decision
--------------
Python 3.14 and a Python 3.12 environment, FFmpeg 9.0.2, pkg-config and Docker
were already present. Cairo and Pango development packages were absent.
An isolated .tools/manim-python Python3.12 environment was created, but the
wheel-only Manim install stopped because pycairo has no usable wheel. No system
packages were installed. The already-running local Docker engine rendered the
scene using the official community image. install.log records the venv outcome.

Official documentation consulted
-------------------------------
https://docs.manim.community/en/stable/installation/uv.html
  Local environment setup; Cairo dependency; optional LaTeX for plain Text.
https://docs.manim.community/en/stable/installation/docker.html
  Official manimcommunity/manim image and volume-based rendering.
https://docs.manim.community/en/stable/tutorials/quickstart.html
  Scene, animation and MP4 rendering workflow.

Storyboard
----------
0–5s: The problem: recover into the certified set, then hand off continuously.
5–12s: One representative trace under u=-1; track and graphs evolve together.
12–16s: Pause at handoff, V=10.092<12; show nonzero velocity and acceleration.
16–25s: Sampled feedback continues the same state toward the origin.
25–34s: Separate universal theorem card with initial box and assumptions.

Verification
------------
The rendered handoff and final theorem frames were visually inspected for
legibility, missing glyphs, clipping, curve/threshold alignment and scope text.
FFprobe confirms a playable H.264/yuv420p MP4. Two PNG frames are supplied for
quick inspection. There is no narration, external publication or upload.
