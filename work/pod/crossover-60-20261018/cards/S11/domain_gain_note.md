# Fixed-r8 terminal gains: independent check and sharper cancellation

This is a separate representation of the UNCHANGED continuous feedback inside the sampled hold, restricted to fixed actuator rate8. It does not establish a variable-rate result, an explicit settling deadline, or a new initial-history contract. Let x denote position relative to the existing center and let w be the complete held-command mismatch plus physical target error. Once clipping is inactive, the source law gives

`x'''+12x''+48x'+64x=8w`.

The original DigitalHold proof already supplies bounded state, bounded mismatch and inactive clipping for its admitted executions. For an infinite fixed-r8 execution, those facts can support the boundedness premise used in the asymptotic argument below. Finite source assemblies alone are not an infinite-execution premise.

## Induced gains

With zero initial state, h(t)=t²exp(−4t)/2 gives x=8h*w. For nonzero initial state add the homogeneous transient, which decays as a degree-two polynomial timesexp(−4t). The exact L∞ convolution gains are:

- position: 8∫h=1/8;
- velocity: 8∫|h'|=2exp(−2)<271/1000;
- acceleration: 8∫|h''|=16(h'(a)−h'(b))<1241/1000, wherea=(2−sqrt2)/4,b=(2+sqrt2)/4.

The velocity derivative changes sign att1/2; h'' changes sign ata,b. `domain_gain_check.py` independently encloses the acceleration gain in[1.2400500302972761,1.2400500302997561] using rational brackets forsqrt2 and rational exponential Taylor tails. Decimal displays are not used for acceptance. The two other rational bounds follow from exact lower Taylor sums: exp2>155/21>2000/271 andexp4>153527/2835>54.

## Stronger command-derivative gain

The proposed intermediate identity `u'=-8v-2a-4u-4w` is correct for the continuous feedback commandu=−8x−6v−a/2. Substitution reveals an exact cancellation:

`u'=32x+16v−4w`.

Thus an acceleration term is unnecessary. More strongly, direct convolution gives

`u' = -4w + k*w`, with`k(t)=128t(1−t)exp(−4t)`.

The kernel is positive on(0,1), negative after1. Its total signed integral is4 and its negative tail integral is−12exp(−4). Therefore

`C = 4+∫|k| = 8+24exp(−4) < 76/9`.

The feedthrough−4 is explicitly included; omitting it would understate the gain. This direct bound is stronger than separately bounding x,v,a or u. No derivative of the uncertain inputw is required.

## Exact original-error/age small-gain arithmetic

Original sensor command error is `8*.001+6*.01+.5*.05=.093`; adding original physical target error.01 givesM=.103. The original total-age bound isτ=.001. A bounded infinite fixed-r8 execution and fading-memory convolution estimates yield

`limsup |w| ≤ M + τ*C*limsup |w|`.

This follows because sample age remains≤τ and the continuous feedback command difference is the integral ofu' over that recent interval. Stable homogeneous transients disappear from the limsup. Splitting the convolution into a fixed recent window and its integrable tail justifies the gain estimate for bounded inputs. The source state/command boundedness is a prerequisite; this algebra alone does not construct a trajectory.

SinceτC<76/9000<1, exact conservative bounds are

```
limsup |w| ≤ 927/8924 ≈ .1038771851 m/s²
limsup |x-c| ≤ 927/71392 ≈ .0129846481 m
limsup |v| ≤ 251217/8924000 ≈ .0281507172 m/s
limsup |a| ≤ (1241/1000)*(927/8924).
```

The implied continuous-command plus sensor bound is less than.431, well below2, as an asymptotic consistency check. The original invariant proof, not this asymptotic calculation, supplies whole-transient clipping inactivity for source-admitted runs.

The result is far tighter than the original weighted-box speed bound.3654m/s, but still does not prove1mm/s precision. A limsup strictly below.029 implies eventual.029m/s containment under these assumptions; it provides no computable time to that point without a transient envelope. Combining this asymptotic reasoning with an explicit initial-state and retained-history convolution bound is the next discriminating proof task.

Evidence: independently checked calculus and exact rational executable bounds. The transfer-function identities, integral evaluations and fading-memory/limsup argument have not been formalized in Lean in this review. The existing source proof remains unchanged. This supplement makes no physical calibration or arbitrary-rate claim.
