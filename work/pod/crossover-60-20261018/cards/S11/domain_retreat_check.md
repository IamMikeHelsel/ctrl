# Independent exponential retreat check

The proposed sharper formula is correct under its stated first-zero/comparison assumptions. Let v(0)=0,a(0)=−A, A≥0, effective targetb≤B withB≥0, and0≤r≤12. At a crossing with

`y(t)=B−(A+B)exp(−12t)`,

we havey≤B and

`r(b−y)≤r(B−y)≤12(B−y)=y'`.

Thus the standard upper comparison givesa≤y, subject to the actual source one-sided ODE/continuity comparison theorem. Integrating twice from zero initial velocity gives

`x(t)−x(0) ≤ B*t²/2 − (A+B)*(t/12−(1−exp(−12t))/144)`.

At t1/12 this simplifies exactly to

`x(1/12)−x(0) ≤ B/288−(A+B)exp(−1)/144`.

ForA6/5,B201/100, the coefficientA+B=321/100 is positive. Therefore a LOWER bound onexp(−1) produces an UPPER displacement bound. The exact rational identity is

`(201/100)/288−(321/100)*(367/1000)/144 = −1923/1600000`.

The required strict exponential lower bound is independently checked by boundingexp(1) from above. The Taylor sum through degree10, plus geometric tail bound

`1/11! /(1−1/12)`,

is1193556233/439084800, which is strictly less than1000/367. Henceexp(−1)>367/1000, and the displacement is strictly less than−1923/1600000m, so the stated non-strict ceiling follows. This is at least1.201875mm of retreat from that first-zero position.

This sharper result uses the same optimistic maximum effective target2.01 allowed by clipping before physical error. It does not assume the actual acceleration stays above−A; that condition is needed only for a different affine-barrier argument, not here. It does assume the actual first-zero acceleration equals−6/5. The actual C8 hold switches before rest and has positive command-arrival velocity51/5000, so this formula cannot be applied at that arrival without addingv0*t. No claim is made that the actual switched C8 first-zero acceleration is−6/5.

Evidence: independent calculus and Fraction arithmetic. The source one-sided comparison/integration bridge remains hand-derived. The inventor's separate Lean arithmetic lemma checks the final conditional algebra; this note does not reclassify it as a full trajectory theorem.
