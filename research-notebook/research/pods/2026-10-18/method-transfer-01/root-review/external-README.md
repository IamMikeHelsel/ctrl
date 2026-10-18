# Ancillary files — "The Erdős n²/25 max-cut conjecture for small multiples of five" (order-10 Horn certificate)

Computer-assisted proof that **a(5n) = n² for all 1 ≤ n ≤ 40** (N ≤ 200), where a(N) is the maximum,
over triangle-free graphs G on N vertices, of the bipartization number β(G) = e(G) − maxcut(G).

## Method (order-10 Horn certificate)
The bipartization density d_mono(W) on the medium band [0.2486, 0.3197] is bounded by 2/25 + δ via an
order-10 (C5-lifted order-9) flag-algebra linear program combining: the per-root-MaxCut envelope at 7 roots
(107 types) and at 8 roots (410 roots), rooted-Horn cuts, the band rows, and a moment block — all over the
12172 band states. The dual is made exact (Python `fractions`). δ_final = 4.8557798×10⁻⁵ <
2/(25·1600) = 5.0×10⁻⁵, so (25/2) n² δ < 1 for n ≤ 40 (2.88% margin), i.e. β(G) ≤ n² for N ≤ 200 via blow-up
integrality (β(G[t]) = t² β(G)). The two density tails use Balogh–Clemen–Lidický (arXiv:2103.14179),
transferred to finite N by the same blow-up.

The moment block is a **manifestly positive-semidefinite Gram** Q = Σ_c w_c vv_c vv_cᵀ with w_c ≥ 0, found by
a plain LP (no SDP solve, no Cholesky rounding); soundness needs only w ≥ 0 together with M^σ(W) ⪰ 0
(Razborov's positivity theorem, the exact G1 Gram certificate).

## Files
- `step1_v2_independent_gate.py` — **independent exact verification** (run `python step1_v2_independent_gate.py`
  from this directory): re-derives δ_final directly from the raw dual, and checks a₇+a₈=1 and w_c ≥ 0
  (manifest PSD). Prints PASS and the closed range.
- `complete_v2_cert.py` — the producer's one-command verifier of all five dual-feasibility conditions
  (needs the full order-10 caches, which are regenerable).
- `moment_gram_lp.py`, `moment_gram_exact_verify.py` — the manifest-Gram moment block.
- `brute_dmono.py` with `flag_engine.py` — a self-contained brute-force max-cut ground-truth checker
  (no certificate needed): the in-band maximum of d_mono is ≤ 0.0556 ≪ 0.0800.
- `g1_exact_psd.py`, `g1_graphon_density.py` — the graphon-level moment-PSD Gram certificate.
- `horn_dual.pkl`, `moment_gram_w.pkl`, `v2_cert_complete.pkl`, `mom_term_exact.pkl` — the compact dual,
  the Gram weights, the verdict, and the cached moment term.
- `SHA256SUMS`.

## Note on the certificate
The moment-Gram LP is non-deterministic; δ_final drifts within roughly [4.75, 4.86]×10⁻⁵ across runs, all of
which give N ≤ 200 robustly (only an occasional lucky run squeaks n = 41 at a 0.05% margin, which we do not
claim). This package is one **frozen** run, δ_final = 4.8557798×10⁻⁵. The full order-10 LP cache and
lifted-state tables exceed arXiv ancillary limits and are regenerable from the scripts.

## Verification status
Independently gated (`step1_v2_independent_gate.py` → PASS, N ≤ 200) and confirmed by the producer's verifier
(`complete_v2_cert.py` → VALID), with the headline bound additionally brute-true on the band — no
false-closure risk.
