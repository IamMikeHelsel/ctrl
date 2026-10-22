# Site animations

Scripts that render the GIFs on the project site. Every frame comes from a closed-loop simulation
that calls `ctrl.robotics`; nothing is keyframed.

| Script | Output | What it simulates |
| --- | --- | --- |
| `render_brake.py` | `brake_shield.gif` | The benchmark braking loop (same barrier, filter and allocator) with and without the shield, toward a dock edge. Wheel forces only act while a wheel is on the dock, so the unshielded robot really falls. |
| `render_arm.py` | `septic_arm.gif` | The 6-DOF arm from `mujoco_benchmarks.py`, min-jerk vs septic (eta = -11), forward and back. Housing color is per-joint winding power. |
| `render_servo.py` | `servo_roll.gif` | Classical point-feature IBVS vs depth-decoupled servoing under a 160 degree roll (`servo_sim.py`). |
| `render_timing.py` | `why_timing.gif` | Per-tick compute time from `bench/socp.py` (Clarabel SOCP) and `bench/tick.c` (generated C99 kernels). |

```sh
uv pip install numpy mujoco matplotlib pillow clarabel scipy
# headless rendering
export MUJOCO_GL=egl EGL_PLATFORM=surfaceless LIBGL_ALWAYS_SOFTWARE=1

# timing data first (needs the generated kernels in out/)
python -c "from pathlib import Path; import ctrl.robotics as r; r.emit_c99_and_iec61131(Path('out'))"
clang -std=c99 -O3 -Iout tools/site_animations/bench/tick.c out/ctrl_robotics_kernels.c -lm -o /tmp/tick
/tmp/tick 3000 > tools/site_animations/bench/tick.txt
python tools/site_animations/bench/socp.py 3000 > tools/site_animations/bench/socp.json

python tools/site_animations/render_brake.py brake_shield.gif
python tools/site_animations/render_arm.py septic_arm.gif
python tools/site_animations/render_servo.py servo_roll.gif
python tools/site_animations/render_timing.py why_timing.gif
```

Fonts: Inter and DejaVu Sans Mono (paths in `common.py`). Encoding uses ffmpeg palettegen.
