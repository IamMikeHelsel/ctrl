# YOLO feasibility and benefit-claim audit

Independent critic assessment, 2026-10-22. AI-written. This is a source review and benchmark design, not a measured YOLO improvement. No model weights, datasets, packages, services or hardware were acquired or run for this assessment. Public documentation is mutable; pin the actual package commit, model/head, export options and backend before reproducing a claim.

**Decision: GO for profiling and one bounded pipeline experiment; HOLD any YOLO speed percentage.** The campaign supplies plausible tools for spatial queries, candidate pruning and uncertainty-aware scheduling. It has not supplied an exact replacement for YOLO's learned convolution/attention computation. A 30% ambition is useful as a hypothesis, not a strict gate or present result. Smaller reliable savings can justify adoption; a larger apparent gain that loses required detections cannot.

## Where the crossover results could apply

| Existing result | Plausible target | What must remain true | Current boundary |
|---|---|---|---|
| M12 fixed geometry represented by intervals; signed template and temporal updates | Repeated occupancy/ROI-intersection queries, downstream spatial association, exact broad-phase rejection | Same predicate, current matrix/geometry, shared ordering; count rebuilding and transfers | Exact restricted Boolean operations, not the real-valued learned network; no real detector workload measured |
| V04 robust rotation certificates; V07/V08/V09 pose and degeneracy checks | Validate a camera-motion/pose estimate before reusing an ROI or track | Source correspondences, calibration, complete uncertainty assumptions and degeneration detection | Certification can add work; objective optimality does not prove physical truth or detector completeness |
| R06 moving-frame derivative transport and correlated bounds | Expand a predicted image region using motion and calibration uncertainty | Valid scene depth/projection, camera/frame derivatives and tracking-error bounds | A world-frame identity does not supply an image-space recall guarantee; inverse conditioning and occlusion matter |
| Controls/S08/S10 timing and uncertainty lessons | Trigger detector refresh before a declared uncertainty/age limit | Bound observation age, missed events, execution delay and invalidation | New objects and disocclusions are not bounded by an existing object's track; periodic/full-frame fallback is necessary unless stronger assumptions are established |
| S12 compact predicate-specific support receipt | Cheap repeated action/ROI admission after offline checking | Same predicate and authoritative current context | The receipt is not interchangeable with full evidence; current measured guard experiment shows no speedup |

M12's Boolean OR–AND operation cannot replace signed floating multiply–accumulate, nonlinear layers or attention merely because both are called matrix multiplication. Its fixed-matrix online assumption also fails when every frame creates a new candidate-overlap matrix unless rebuilding is charged. Arbitrary bounding boxes do not automatically form small unions of intervals under one shared order. Dense overlap, changing candidates and fragmented masks are required adversaries. The relevant current evidence is M12's scoped card (research-checkout provenance: `work/pod/crossover-60-20261018/cards/M12/CARD.md`; not included in this main-branch package), not a general matrix-multiplication result.

A more promising exact transfer is a broad phase that proves some box pairs cannot overlap, then runs unchanged IoU/greedy suppression on the remainder. A Boolean conflict test alone does not preserve greedy NMS: if A suppresses B, B overlaps C, and A does not overlap C, suppressing C merely because B has a higher score is wrong for greedy NMS. Preserve score order, tie policy, class handling and threshold equality.

## Current primary-source baseline

Ultralytics exposes separate preprocess, inference and postprocess timing in the predictor. Those intervals do not automatically include capture, buffering, every host/device transfer, visualization or consumer delay; timestamp capture-to-consumed-result separately. Frame-stride and buffering settings can trade temporal coverage or observation age for apparent throughput. [Predictor source reference](https://docs.ultralytics.com/reference/engine/predictor), [prediction settings](https://docs.ultralytics.com/modes/predict).

The current YOLO26 guide says the ordinary prediction path uses its one-to-many head with NMS, while `nms=False` selects its one-to-one NMS-free path. This is an architecture/head choice whose accuracy must be remeasured, not a free identical-output substitution. YOLOv10 already studied NMS-free dual assignments in 2024. Therefore “remove NMS” is neither a new campaign invention nor applicable to every chosen deployment. [Current end-to-end guide](https://docs.ultralytics.com/guides/end2end-detection), [YOLOv10 primary paper](https://arxiv.org/abs/2405.14458).

The existing NMS implementation already has early termination and a separate Fast-NMS path. A custom spatial query should beat the actual optimized baseline, not a Python all-pairs strawman. TensorRT export already provides conventional compilation, precision and fusion opportunities; engines depend on target/runtime and reduced precision needs accuracy validation. Charge these as established baseline optimizations rather than evidence for our math. [NMS source reference](https://docs.ultralytics.com/reference/utils/nms), [TensorRT integration](https://docs.ultralytics.com/integrations/tensorrt).

Tracking is not automatically detector skipping. Existing tracker settings include optional appearance and motion-compensation work, which must be included when evaluating savings. Sparse key-frame recognition and propagated features are longstanding prior art; Deep Feature Flow explicitly evaluates that approach. Our possible contribution is a source-bound uncertainty/refresh contract or better workload-specific implementation, not the idea of exploiting temporal coherence. [Ultralytics tracking documentation](https://docs.ultralytics.com/modes/track), [Deep Feature Flow, CVPR 2017](https://openaccess.thecvf.com/content_cvpr_2017/html/Zhu_Deep_Feature_Flow_CVPR_2017_paper.html).

## Three discriminating benchmarks

### 1. Exact structured spatial query, before touching inference

Freeze a recorded detector-output workload and its downstream question: for example, whether any active occupancy pixel intersects each declared disk/ROI. Compare vectorized/GPU baseline, interval-prefix queries and incremental signed-template queries. Include dense/fragmented masks, moving geometry, empty frames, boundary equality, stale geometry, high Hamming change and fixed versus changing camera transforms.

Require identical results for every query under the same boundary convention. Measure complete representation construction/update, input/output, CPU/GPU transfers, memory and query time separately. Use realistic candidate/ROI counts, plus adversarial extremes; report crossover sizes rather than only the best case. A successful local kernel is worth keeping even below 30%, but only claim pipeline savings after measuring its actual fraction of total cost. This is the lowest-risk bridge from an already checked campaign mechanism.

### 2. Exact NMS broad phase, only if profiling makes it relevant

Keep the same frozen model, tensor outputs, confidence threshold, class policy, precision, score/tie convention and greedy reference. Test a spatial index/interval broad phase that removes only pairs with certified zero intersection; verify identical retained indices and boxes. Include the three-box suppression chain, equal scores, threshold ties, huge boxes, dense crowds, all-overlap, rotated boxes if supported, and max-candidate truncation. Changing NMS semantics is a separate accuracy experiment.

Compare to the existing optimized NMS and measure rebuild cost each frame. Also report the chosen model's NMS-free head as a separate accuracy/latency comparator where available. If NMS is already a negligible stage, or the selected head is NMS-free, do not pursue this route as a neural-forward speedup. No theorem currently establishes a universally small interval representation for these overlap graphs.

### 3. Bounded refresh / ROI scheduling for video

Compare four causal policies on the same chronological clips: full detection each frame; fixed stride; ordinary tracking plus periodic full refresh; uncertainty-aware refresh with tracked-ROI expansion and periodic full-frame fallback. Keep detector weights fixed initially. Freeze the policy using training clips; test heldout scenes without future-frame access. Explicitly count detector calls and actual tensor dimensions: cropping then resizing every crop to the old full input size may save no neural work and can multiply calls.

Adversaries include sudden entry outside every ROI, occlusion/disocclusion, camera cuts, fast small objects, stationary-then-moving objects, blur, illumination shifts, stale calibration and schedule stalls. Measure mAP50–95, per-class/small-object recall, new-object time-to-first-detection, consecutive-miss duration, false positives, ID switches/HOTA where tracking matters, result age and deadline misses. Predeclare task-specific noninferiority limits and confidence intervals; do not select them after viewing speed results. A generic detector cannot guarantee unseen-object recall from prior tracks alone.

This has the greatest plausible whole-pipeline headroom because it reduces expensive calls, but it is also the largest semantic change. It requires an application wrapper and tracking/scheduling integration; it is not a drop-in faster YOLO forward pass or physical safety proof.

## Timing, Amdahl accounting and the 30% aspiration

For a serial baseline, let f be the measured time fraction improved, s its speed factor and o added overhead as a fraction of baseline time. Then

`new_time / old_time = (1 - f) + f / s + o`.

If NMS is 10% of time and becomes 10× faster with zero overhead, total time falls 9%, not 90%. If a stage is 40% and becomes 4× faster, total time falls 30%. These are arithmetic scenarios, not measurements. Removing a stage entirely cannot save more than its measured fraction. For concurrent GPU/CPU pipelines, use the measured critical path and queue behavior; summing overlapping stage times is invalid.

“30% faster throughput” means 1.3× throughput (23.08% less time under a fixed serial workload). “30% lower latency” means 0.7× time (42.86% more reciprocal throughput only without another bottleneck). Name the quantity. A 10% reduction followed by a 20% reduction of the remaining same cost yields 28%, not 30%. Independent savings on disjoint baseline components use their baseline weights; overlapping pruning/skip optimizations can remove the same work and must not be double-counted. Measure combined configurations and interactions.

Freeze hardware, power mode, clocks policy, model/version/head, backend, tensor shape, batch, precision, thresholds, camera/frame schedule and dataset. Record warm-up and steady state separately, synchronized device timings, end-to-end p50/p95/p99, throughput, dropped frames, queue age, CPU/GPU memory and energy per valid processed frame/task. Pair runs on the same clips with randomized order, sustained thermal conditions and uncertainty intervals. Existing optimized deployment is the primary comparator; report an unoptimized migration baseline separately if useful. No run was performed here.

## Shake, energy, temperature and stacked benefit claims

| Claim | Required outcome measurement | Why a proxy is insufficient |
|---|---|---|
| Less shake | Tool/camera pose error, acceleration spectrum around structural modes, settling time and image blur on matched motion/payload | Lower jerk is not a universal ordering of vibration for different plants, frequencies or tracking loops |
| Less energy | Electrical energy at a named drive/board port per successful matched task; regeneration/storage/auxiliaries and rejected tasks counted | Lower jerk, FLOPs, peak current or runtime alone does not determine joules |
| Lower temperature | Winding/drive/board temperature rise and peak at matched ambient, cooling, duty cycle and thermal steady state; validated model if not measured | Energy reduction need not translate proportionally into temperature; location and time distribution of losses matter |
| Faster perception | Capture-to-result age and valid task throughput with recall/quality constraints | Skipped frames, lower input resolution or buffered stale outputs can create misleading FPS gains |

R08 already supplies matched-model counterexamples to jerk-only energy ranking, including voltage-feasibility and regeneration boundaries. The local modeled energy improvement can be described with its explicit parameters; it cannot be converted into a robot energy, vibration or temperature percentage. R06 similarly shows that small pose error need not bound derivative error. R08 evidence (research-checkout provenance: `work/pod/crossover-60-20261018/cards/R08/CARD.md`; not included in this main-branch package), R06 evidence (research-checkout provenance: `work/pod/crossover-60-20261018/cards/R06/CARD.md`; not included in this main-branch package).

Do not add percentages across shake, energy, temperature and speed: these have different denominators and can conflict. A multi-objective score needs an explicit user utility and feasibility constraints. Keep each metric, baseline, uncertainty and evidence level separate. Treat 30% as a notional stretch target, while accepting a smaller measurable benefit with low integration cost and preserved behavior. State larger system gains as conditional hypotheses until the combined stack is tested.

## Packaging wording and next gate

Supported: **“We have checked mathematical components that may reduce repeated spatial-query and decision work. Next we will test whether they improve a specified YOLO-based perception pipeline while preserving its detection requirements.”**

Unsupported today: “Our math makes YOLO 30% faster,” “formal proofs guarantee detector recall,” “smoother motion saves 30% energy and heat,” or “the individual gains stack to 30%.” No campaign result, current source review or paper comparison establishes those statements.

Recommended next gate: obtain the already-used model/configuration and an authorized existing workload, profile the actual critical path, then choose one of the three benchmarks. No need to acquire weights or new services merely to show activity. Quality of this feasibility assessment:18/20 (90%; source fidelity4, crossover mapping4, discriminating tests4, claim critique4, deployment readiness2). Confidence is qualitative: high that the current evidence does not establish a forward-pass speedup; practical pipeline benefit remains unmeasured.
