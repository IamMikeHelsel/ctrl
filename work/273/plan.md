# Erdős 273: conditional capacity and smooth moduli

Research target: establish a new structural restriction on a hypothetical strict covering
with distinct moduli m=p−1, p≥5 prime. The full existence problem is not solved here.
Primary target: https://www.erdosproblems.com/273

The selected experiment excludes an infinite family by retaining the geometry of a small
prefix of congruences and bounding everything else. This differs from merely searching
larger least common multiples. The connection to the earlier controls work is conditional
resource accounting: a global budget can look feasible while no allocation can satisfy
every surviving local constraint.

1. Audit current results and avoid other active research lanes. Completed.
2. Check the conditional-capacity identity independently. Completed by program manager.
3. Search 7-smooth and 11-smooth families with exact rational arithmetic. Both exclusion
   tests completed; seven-smooth now also has a complete kernel-checked theorem; eleven-smooth remains Python evidence.
4. Independently replay a small 7-smooth certificate and reject corruptions. Completed.
5. Kernel-check its finite sieve, capacity table, and arithmetic. Completed, including the
   integrated build. Complete statement assembly has now passed as well.
6. Connect finite certificates to arbitrary finite congruence families using a CRT counting
   lemma, translation normalization, exponent-box coverage, and a geometric-tail bound. Completed in CoveringFamily.lean.
7. Run the robotics tremor experiments next, per Mike's latest priority. Eleven-smooth is secondary. Continue scoped novelty review; no priority claim yet.

The exploratory 13-smooth extension is secondary. A timeout or a surviving bound is not a
covering witness, nor evidence that a covering exists. Do not edit Challenge files, mark a
problem solved, approve a statement, or submit results externally as part of this work.

The bounded overnight research round and morning report are complete. Automation
`erd-s273-overnight-proof-and-review` is paused; scheduler state confirms no next run.
The 07:30 Pacific October 19 report is `work/vision/morning-report-2026-10-19.md`.
The final independent audit found no drift in the saved theorem or experimental evidence.
No automatic continuation or next-day occurrence is scheduled.
The earlier hourly schedule was paused after Mike objected and replaced only after
his explicit request for specific overnight self-checkins. Priorities are full
theorem assembly and novelty review, followed by robot tremor experiments; eleven-smooth is secondary, with independent program-manager reporting.

Reproduce the small independently checked certificate:

```sh
uv run python work/273/check_seven.py --self-test --output work/273/seven-certificate-audit.json
uv run python work/273/smooth_probe.py --primes 2,3,5,7,11 --caps 14,9,6,5,4 --prefix 4,6,10,12,16,18,30,36 --output work/273/probe-11-symmetric.json
```

The baseline eleven-smooth run without the extra stabilizer reductions is saved in
`probe-11-deep.json`. It agreed with the faster run; the code now includes the reduction.

Author baselines inspected: https://github.com/veljjanoski/erdos273 and
https://github.com/idealombrer/erdos-273-covering-pm1 . Their claims are prior-art context,
not independently reproduced results of this session.
