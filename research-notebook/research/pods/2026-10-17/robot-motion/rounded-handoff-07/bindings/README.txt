EXACT NATIVE REFERENCE BINDING

The 12 NativeData lists encode the frozen native-execution-06 reference export.
There are 886 pieces and 874 adjacent joins. Durations and polynomial coefficients
are exact rational values. Floating coefficients are converted from their stored
binary values, not rounded decimal display values.

NativeData checks positive duration, |jerk| <= 7.5, initial rest, contiguous clock
intervals, the final horizon, and all three transformed reference-jump bounds.
All 12 concrete checks use Lean's kernel decision procedure.

NativeBridge proves list-index extraction and the rational-to-real cubic link.
It calls the physical finite-handoff theorem. NativeInstances supplies 12 named
conditional position certificates. The builder's separate NativeCoverage and
NativeGlobal modules extend the result to every absolute time in the horizon.

The common bound is 0.128125000188 mm relative to each exported reference. It
uses sigma=10/s, disturbance <=0.01 m/s^2, local jerk <=7.5 m/s^3, initial radius
41/320000 m, and at most 188 join allowances of 1e-15 m. Each allowance bounds
the position, scaled velocity, and scaled acceleration combination at a join.
It was selected after inspecting frozen data. No numerical run was retuned.

The actual scalar plant, feedback, rate/disturbance bounds, initial error cube,
and physical-state continuity remain assumptions. This is not a proof of the
native planner, JSON parser, firmware, robot model, task hold, or physical rest.
The independently checked JSON-to-Lean value binding is outside the Lean kernel.
All old task failures and the failed gate05 are retained.

Independent acceptance: ../grader/review-report.txt. Its frozen manifest is
df6e5b52f528875b6bbc2fd6d3a12a0dbeee6107bd7a7cc8898b994c843ed4af.
The reviewer rebuilt the local sources, audited standard axioms, replayed the
kernel, checked every source coefficient, and rejected altered input data.

exact_reserve.py supplies a separate exact Python rational audit. Its tighter
sum is numerical data evidence; the Lean instances use the conservative uniform
allowance. generate_lean_data.py regenerates NativeData from the frozen export.
The source-freeze file binds the three Lean modules before independent review.
Development logs are diagnostic history, not the independent acceptance record.
Compiled objects are disposable and are not part of the repository snapshot.
