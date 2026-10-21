# V01 root PM — contracts for transferring projective claims

AI-written. Four reused roles run on inherited working model; exact model ID unavailable. Original sources remain unchanged. Source4.36 compiler exists but Mathlib compiled cache is unavailable; byte-identical isolated source copies were successfully rebuilt under existing4.33 cache. This is a different-toolchain replay, not a pinned4.36 validation.

## Exact question and correction

Which projective incidences and plane-induced image constraints survive camera-frame change under explicit nonzero, depth and invertibility conditions? Original vector identities are valid but do not by themselves package a nonzero projective quotient, oriented rays, physical visibility or calibrated pixel-error semantics. Plane n·X=d, d≠0 excludes the first camera center; it does not exclude the second. Domain's determinant bridge and critic's visible collapsing-ray example expose that distinction.

The source proposal's statement that epipolar geometry is valid only for nonplanar points is false. The physical epipolar equation still holds for coplanar points. Planar ambiguity in an uncalibrated fundamental matrix must be distinguished from calibrated essential-matrix constraints. Primary authors' [epipolar chapter](https://robots.ox.ac.uk/~vgg/hzbook/hzbook2/HZepipolar.pdf), pp239–243, explicitly separates scene-independent geometry and plane-induced transfer avoiding both centers. No source prose was edited during this review.

## Root quantitative camera fixture

R=[[3/5,0,4/5],[0,1,0],[-4/5,0,3/5]], t=(1/5,1/10,2/5), planeZ2, so H=[[3/5,0,9/10],[0,1,1/20],[-4/5,0,4/5]], detH=6/5. On |u|≤1/2,|v|≤1/4, canonical homogeneous heightq3 lies[2/5,6/5], targetdepth2q3 positive, projectedx∈[1/2,3],y∈[−1/2,3/4]. Exact physical corner checks preserve point/plane identities.

For lineu0, inverse-transpose line is(2/3,0,−3/4). Unnormalized incidence pairing is invariant. After homogeneous normalization, equal source residualmagnitudes1/2 become5/12 and5/4. A constant raw algebraic-residual threshold is not preserved. The transported threshold is tau/|q3|, with chartnonzero required. Positiveheight special case belongs to the declared canonical physical gauge. H→−H preserves pixels but flips rawheight; estimatedH=alphaHphysical must divide rawheight byalpha to recover physicaldepthratio. Generic division identities in Lean remain algebraically valid atz0 because division is total; they do not license a geometric zero-height chart.

Nine exact calibrated examples useK1=(800,1000 principal320,240), K2=(900,1100,skew50,principal300,200). CorrectpixelhomographyK2HK1inv maps centralpixel(320,240) to(10525/8,1075/4). Applying normalizedH directly to pixels fails. This is a type/convention negative, not a bug claim about the source's calibrated-ray theorem.

## Robust quotient transfer

With only third-row errors≤.001, all patchheights remain≥1593/4000. This alone gives no accuracy bound on projectedpixels or transformedlines: other rows could be arbitrarily wrong. Under the stronger explicit hypothesis that all9entries have error≤.001 in the same fixed gauge, each row error≤7/4000. Exactquotientidentity gives

    image_error_i=(delta_i-image_i*delta_z)/(height+delta_z).

The wholepatchbounds are28/1593 horizontally and49/6372 vertically. Exact2048corner cases pass and onecorner attains both. The universal proof uses boundedrowerrors/knownimagebounds/positiveheight, not a claim that finitevertex sampling alone proves a rational-function bound. Root's generic ratio lemma formalizes the key quotient step, with remaining fixture assembly tracked separately. A generic perturbed matrix is not asserted to have an exact physical pose decomposition under fixed calibration.

## Robotics coordinate-type transfer

A passive translation addsb to both scene point and camera center; their raydifference is unchanged. ForX=(1,0,1),b=(1,0,0), naive normalization of newpoint(2,0,1) yieldspixel2 while correct point-minus-newcenter ray yieldspixel1. Plane normal and offset must share any nonzero scale. These simple negatives motivate a typed contract for points, directions, planes, calibration and opticalaxis, rather than an undifferentiated matrix transport. Inventor's passive orthogonal-frame fixture independently preserves depth only when the opticalaxis and plane covector are transported too.

## PM boundary

GO for a source-bound admissibility/refinement layer with20semantic tests after breadth. Preserve dnonzero, secondcenter exclusion, raynonzero, calibrationinvertibility, depthorientation, active/passive meanings, chartmargin and gauge. Keep pure incidence separate from numerical residual or physical visibility. No new projective geometry theorem, physical calibration, occlusion inference, detection or robotic execution is claimed. Exact/kernel evidence and compiler/dependency limits are in individual ledgers.
