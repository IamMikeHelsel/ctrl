# C11 PM synthesis

AI-written pod: root PM, inventory_math domain, inventory_vision_robotics inventor,
inventory_controls_safety critic. All inherited root model, exact identifier unavailable.
No alternate-family/Spark inference. Original source files and toolchain pins preserved.

Question: Can active-facet geometry yield a less conservative full-state entry test
than independent box bounds for the tilted hold cube?

The source C3 uses z=(x−c,x−c+v/4,x−c+v/2+a/16), R=.055525,
c=m_x+m_v/4+m_a/32 frozen once, sensor errors(.001,.01,.05), pending−1.21,
D≤.0005, rate[8,12], targeterror±.01 and global reading age≤.001.
Its old guard is |m_v|≤.02,|m_a|≤1.25. Its exact two-sided Execution retains
one physical state and the left-pending/right-dispatched convention at D.

Prior active_facet_screen instead studies a weighted-cube shrink under another
residual budget. It is not an already proved entry theorem. Primary pinned
FiniteMinimum.lean is inspected at
https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MassAction/FiniteMinimum.lean.
It requires every active branch derivative; inactive branches need continuity.
No whole-family149 review, new chemical theorem implementation or novelty claimed.

## Discriminating results

1. Universal containment in an intersection of facets equals separate universal
   facet tests. Maxima need not occur at the same state. Removing a facet's valid
   worst corner because another facet peaks elsewhere is unsound. Root kernel
   checks this quantifier swap and a tied-face escape where one active face moves
   inward while another moves outward.
2. The exact time-zero robust guard at the ORIGINAL center is
   |8m_v+m_a|≤928/625 and |m_a|≤2081/1250. Domain kernel-proves the iff over
   the complete sensor box. It is larger than the old rectangle, but cannot by
   itself replace delayed admission. The legal reading m_v=−.2,m_a=.1152 with
   all three negative sensor errors starts on z2=−R and has z2′=−.815 for
   pending r8,error0. Critic supplies an explicit finite-time outward formula.
3. A selective positive band m_v∈[.029,.030],m_a∈[1.23,1.24] does improve
   admission while keeping center/controller/age/sensors unchanged. Signed pending
   flow bounds yield startup|z_i|≤.055375, margin.00015, whereas symmetric drift
   inflation yields.056665325>R. Feedback slope≤7.1732<8. Simply raising the
   old speed cap to.03 fails at m_a=1.25 by.0001625 at time zero.
4. Root extends the positive band to the polygon m_v≥.02, .15≤m_a≤1.25,
   8m_v+m_a≤1.48. Initial a∈[.1,1.3],v∈[.01,.17625]; the pending ODE yields
   a∈[.08488,1.3],v∈[.00935,.1769]. First two tilted coordinates remain negative
   and increase. The third decreases and may cross zero, but its lower bound
   −.000052825 is far above−R. Same startup bound.055375; feedback range
   [.7848,7.2452]. Independent32corner and derivative-vertex replays agree.
   Exact hand trapezoid area.08525 plus old rectangle.1 (boundary overlaponly)
   gives85.25% extra nominal measurement-plane area for the UNION. This is not
   acceptance probability, practical performance, a formal measure theorem or safety.
5. A separate prospective center policy solves a one-dimensional robust Chebyshev
   problem. Using the old C3 pending envelope at m=(.14,−.01,−1.17), support
   U=.141177825,L=.051464675 gives minimax center.09632125 and radius.044856575.
   Choosing center U−R+.001=.086652825 gives a hypothetical fixed-R ceiling
   .142177825, versus old.1564625. This changes the actual first command from
   .3325 to.2182226, so it is NOT an unchanged-Execution clearance result.
   Independent24corner replay and generic kernel minimax/feasible-interval lemmas
   establish geometry only. Original detector and existence gaps remain.

## Three materially distinct transfers

Polyhedral support/linear duality removes conservatism in the measurement guard
while retaining every valid facet witness. Directed reachability under a known
pending command replaces symmetric drift inflation; it preserves the ODE and
uncertainty quantifiers and fails if the pending sign/rate/age or retained state
changes. Robust facility-location/Chebyshev centering reallocates position slack
and exposes a clearance-versus-center-policy tradeoff. The deliberately unexpected
lesson from active-branch chemical barriers is a negative: ties demand all active
branches, and correlated measurements cannot justify deleting separate universal
obligations. It does not supply automatic detector liveness.

## Formal boundary and gate

Domain freshly compiles a source-bound acceleration invariant under actual Execution
with initial|a|≤1.3, without fabricating the old Guard. Inventor's two source-bound
adapters prove the original prefix budget and all-time cube from explicit whole-prefix
startup cube and pending right-slope≤8. They preserve source center, global age,
clipping, radius and dispatch conventions. The new band's/polygon's mean-value,
signed-facet and slope composition is independently reviewed hand mathematics plus
kernel scalar pieces; it is not yet one complete source-bound Lean theorem.
Source adapters use pinned4.35 with hashmatched historical cached dependencies;
new scalar helpers use repository4.33.1. Final independent ledger determines what
is accepted; failed/unfinished compilations are excluded.

GO for the selective coupled/directional guard and a source-bound composition test.
NO-GO for blanket widening, initial containment alone, or simultaneous-maxima deletion.
After all60 reviews, a30minute block should compose the polygon measurement guard,
actual startup ODE estimates and existing conditional all-time adapter, then independently
reject20 mutations. Keep prospective center optimization as a separately typed branch.
No detector, general execution existence, precision rest,15cm clearance, coupled robot,
contact or hardware validation is established. At mx=.14 the smallpositiveband's
old-center tube can reach.241775, so admission is not useful clearance by itself.

Quality4/4/4/4/3=95/100. Subjective confidence high for scoped exact/kernel algebra,
uncalibrated for closed source composition and practical utility. No novelty claim.
