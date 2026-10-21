# Independent audit of the scoped septic reference

Audited producer Python SHA256 `f8a087bc557f2c9dab0670f26dbf920cd3f3c05e9853ed46c5a01a5286b4a90d`, saved input/output in `inventor_septic.json`. The producer may subsequently be revised; these observations describe that exact version. No producer file was edited or executed for its output side effects. The gate function alone was extracted with AST and evaluated in isolation. `pm_septic.lean` was read for statement scope; its compilation was not presumed from existence.

## Positive reference is kinematically sound

Retain rest during the specified5ms latency. Then use `q=D f(s)`, `s=(t−ell)/T`, `T=1/10`, `D=1/24000`, and `f=35s⁴−84s⁵+70s⁶−20s⁷`. Hold q=D after the absolute deadline21/200. Both endpoints have the required zero velocity, acceleration and jerk; the joins to the rest pieces preserve q,v,a,j continuously.

Independently differentiated coefficient lists agree through snap. With z=s(1−s), r=1−2s, `f'=140z³≥0` on[0,1]. Together with f(0)=0 and f(1)=1, this proves the continuous corridor `0≤q≤D`. A finite sample grid is not used as the reason for this corridor claim.

The declared bounds are correct: velocity7/7680, acceleration7/64 (conservative), jerk35/16 and snap350, below1,3,10,400 respectively. One independent proof of the snap bound uses

`f''''/840=(5r³−3r)/2`,

`1−(5r³−3r)/2=(1−r)[5(r+1/2)²+3/4]/2`,

`1+(5r³−3r)/2=(1+r)[5(r−1/2)²+3/4]/2`.

Both right sides are nonnegative for −1≤r≤1. Thus the snap bound is continuous on the moving segment and holds almost everywhere on the whole reference. The exact script checks these identities and1001 rational diagnostic points; the factorizations supply the all-time argument.

## Joins and retained history

Snap is0 in rest,350 immediately after motion begins,−350 immediately before motion ends, and0 afterward. Therefore this is C3 position with Lipschitz jerk and bounded snap almost everywhere. It is not C4, does not have continuous snap at the joins, and cannot meet a bounded-crackle requirement without a different reference. The preserved initial state must truly be(q,v,a,j)=0; the gate correctly returns UNKNOWN for nonzero incoming jerk. It cannot justify resetting a nonzero jerk or other state at execution.

The position corridor is a reference corridor, not a physical tracking guarantee. Since the reference touches both corridor endpoints, an arbitrary symmetric nonzero physical tracking tube cannot be contained in[0,D]; at the final endpoint a positive position error leaves the interval. This does not invalidate ADMIT_REFERENCE under its declared scope.

## Consumer boundaries found in the audited prototype

1. A negative latency request `ell=−1/200` actually returns ADMIT_REFERENCE. This is outside causal hold semantics and needs an explicit nonnegative-latency check before the gate is used as an input consumer. The positive frozen example is unaffected.
2. Added fields requesting an external corridor[0,D/2] or continuous snap also return ADMIT_REFERENCE because those fields are outside the current prototype schema and ignored. The reference violates those added requirements. This is not a refutation of the scoped polynomial: either the outer schema must reject unsupported constraints, or the consumer must explicitly bind the required corridor and smoothness contract before its admission label can apply to a general task.
3. The initial-state string check is conservative and does reject the tested incoming jerk1. It does not independently establish that the supplied state matches actual retained history; that binding is an upstream obligation.

The correct positive label is **ADMIT_REFERENCE for the explicit rest-to-rest, forward corridor[0,D], bounded-a.e.-snap contract**. It is not acceptance of arbitrary full-state requests, arbitrary corridors, continuous snap, bounded crackle, or a robot trajectory. UNKNOWN remains a lack of this particular sufficient certificate, not proof of infeasibility.

Recommended final gate: preserve the positive example and failed prototype probes; validate latency and supported schema explicitly, then independently re-run the positive and negative cases. Keep polynomial derivative/interval reasoning separate from the scalar budget arithmetic and any later plant certificate.

## Repaired gate independently replayed

Final audited producer SHA256 `5855394567dba60905e0d60c20532086ee962419f5a922066e4b91b9505b2197`: all17 saved cases independently reproduced by extracting the gate without module side effects. Eight additional probes and a missing-regularity probe passed: negative latency, continuous snap, unexpected continuity fields, nonzero incoming jerk, late commit and missing regularity return UNKNOWN; narrower or initial-state-excluding corridors return REJECT. A zero-distance rest request remains correctly admitted as a reference. The positive example retains the same exact derivative budgets.

The final consumer now checks exact supported keys, nonnegative latency, declared `AC_jerk_bounded_snap_ae` regularity, and a corridor containing both initial and goal positions. This repairs the observed semantic gaps for its supported rational-input schema. It is still a prototype rather than a total parser for malformed field types or fraction strings. Failed-prototype evidence remains in `inventor_septic.json`; repaired replay is separately saved in `inventor_septic_final.py/json`.
