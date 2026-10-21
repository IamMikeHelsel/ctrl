# Capsule comparison and strict-superset repair

Let E_R={z:zᵀPz≤R}, g=(1,−1,1), and K(R,d)=E_R+[-d,d]g. For any covectorp,

    h_K(p)=sqrt(R pᵀP⁻¹p)+d|p·g|.

This follows by maximizing the two summands independently. It shows K(11,1/8) is NOT a superset of E12: p=(1,1,0) has p·g=0, so the capsule keeps E11's strictly smaller support in that direction. An exact rational witness is z=7P⁻¹p, whose energy127050875/11131832 lies strictly between11 and12, while its p-projection exceeds K(11,1/8)'s maximum. Conversely(73/40)g lies in that capsule outsideE12. Thus the two sets are not nested.

Volume can be computed without sampling. Integrating parallel chords along g shows addition of[-d,d]g increases volume by2d||g|| times the ellipsoid's projected area on g-perpendicular. That area isπR sqrt(gᵀPg)/(||g||sqrt(detP)), using the determinant of the projected inverse quadratic form. Therefore

    vol K(R,d)=π/sqrt(detP) [4R^(3/2)/3+2dR sqrt(gᵀPg)],
    gᵀPg=189/50.

K(11,1/8) has volume ratio≈.97410611995 toE12: about2.59% SMALLER, despite extending beyond it in some directions. Rational outward bounds sqrt11<3317/1000, sqrt(189/50)<1945/1000, sqrt12>3464/1000 give rigorous ratio<647977/665088<1. The geometric volume formula is a hand proof; its radical/arithmetic bound is checked in domain_capsule.lean. No trajectory probability is inferred from volume.

A better variant uses the **unchanged original E12 core**:

    K+=E12+[-1/25,1/25]g.

The sharp source-P position bound gives|xcore|≤49/25, since12σ<(49/25)². Adding|δ|≤1/25 retains|x|≤2. K+ containsE12 byδ0 and is a strict superset: core(89/50)g has energy1497069/125000<12, whereas adding(1/25)g gives(91/50)g with energy1565109/125000>12. Its volume ratio is

    1+(3/50)sqrt(63/200)≈1.03367491648,

an increase of about3.37%. This is a true volume and inclusion improvement, although it reaches less far along g than the earlier E11 capsule.

The new set also contains a genuinely CLIPPED state outsideE12. Start with the minimum-energy request2 state zmin from domain_geometry.json, use core=zmin+(11/20)g and lift=core+(1/25)g. Exact values are recorded in domain_capsule_active.json. Core energy39402999991/3306780000<12; lifted energy999324576151/82669500000>12; both requests equal2 and clamp values equal1.

The preserved dynamics require no new physical assumption beyond the source model: c·g=0 and the open-loop held plant satisfiesA0g=−g. Thus equal held drive/disturbance sends an initialδg offset toδexp(−t)g, with identical initial clamp commands. At sample boundaries the same property repeats, so the two trajectories use identical command traces under the same admitted clock/disturbance sequences. The offset amplitude decreases and remains within the capsule segment. Root owns the actual-source execution theorem; domain's geometry and volume calculations do not substitute for it. Disturbance may be any source-admitted sequence; there is no claim of arbitrary within-hold variation or altered plant parameters.

Files: domain_capsule.py/json (exact support/witness checks and labeled numerical volume), domain_capsule.lean (four scalar geometry/volume arithmetic statements), domain_capsule_active.json (clipped strict-expansion witness). These supplement, and supersede any implication that the E11 capsule is a volume expansion in, domain.md.

Independent source-bound acceptance: original notebook Lean4.35 compiled critic_source_bridge's three E11 execution lemmas and critic_source_position's three sharp-position/core bounds, including actual-source E12→49/25. All printed axioms are standard. Logs are domain_critic_source_bridge.log and domain_critic_source_position.log. No pin or original source was changed. These checks validate the source-bound core/position ingredients; root's capsule execution theorem remains separately owned and reviewed.
