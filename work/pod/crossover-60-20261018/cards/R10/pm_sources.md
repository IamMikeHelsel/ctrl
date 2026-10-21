# Source and comparison scope

Primary status check19October2026: Ruckig official documentation https://docs.ruckig.com/ describes state-to-state motion constrained by velocity, acceleration and jerk; its associated paper is Berscheid and Kroeger, RSS2021, https://arxiv.org/abs/2105.04830. This supports using a capable native online trajectory generator as the benchmark. It does not supply a physical tracking/deadline proof for this scalar actuator model.

The original08 report supplies historical18/24 native versus6/24 FIR valid-task counts, a two-resolution scalar batch and independent high-precision replay. Those historical results are not rerun native planning in this campaign. New revision widths are post-source candidates; their original FIR first event and complete physical prefix remain unchanged. A successful new trace is not a general competitive or time-optimality result.

The current reference certificate uses exact rational interval polynomials and an independently checked coefficient representation. Source-bound all-time physical deadline/remain verification is still absent. The full task includes initial progress, causal readiness, reference V/A/J, endpoint tolerances and remaining through2.5s; a failed revision cannot earn success merely because the old reference is tracked accurately.
