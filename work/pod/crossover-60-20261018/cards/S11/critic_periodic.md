# Period-two terminal-history countermodel

This is a hand-derived sampled-hold countermodel, not a claim that the actual C8 guard/pending prefix reaches this orbit. Initialize the delayed controller history consistently with the orbit. The original finite/global C8 initialization is a separate obligation.

Take h=1/2000, r=8, E=exp(-rh), C=(1+E)/(1-E), D=2/r-Ch, and A=1/100000. At successive dispatch boundaries prescribe

- a_n=A(-1)^n,
- v_n=-D a_n/2,
- x_n=c+D a_n/(2r).

Hold effective target b_n=-C a_n during cell n. The exact held-lag solution gives a_(n+1)=-a_n. Its integrated velocity increment is D a_n, so v_(n+1)=-v_n. Its position increment is -D a_n/r, so x_(n+1)-c=-(x_n-c). These are direct substitutions into the analytic held-flow formulas; no numerical limit argument is used.

One-cell delayed exact state readings have deviations opposite the current state. Therefore the unchanged source feedback computes u_n=a_n[1/2+D(4/r-3)]. Set delta_n=b_n-u_n. This is a bounded cellwise constant target-error sequence, with no future state access needed: the entire alternating sequence can be fixed initially.

`critic_periodic.py` bounds E by rational positive-exponential Taylor sums plus geometric tails, then inverts. Exact endpoint arithmetic gives |delta_n| about .005005006675 <.01, |u_n| about .00000500000834 <2, |v_n| about1.6666662e-12>0 and |a_n|=1e-5. Thus a consistent terminal sampled-feedback history can remain bounded forever without converging to exact rest. The tiny motion is not evidence against any specific larger tolerance such as1mm/s. The acceleration has a nonzero alternating subsequence, so exact maintained rest and convergence to zero are excluded for this history.

This does not establish actual C8 reachability, a periodic limit of the later square-wave probe, or a Lean theorem for the trajectory. Source initialization, the first pending command, and guard membership must not be silently substituted by this periodic history.
