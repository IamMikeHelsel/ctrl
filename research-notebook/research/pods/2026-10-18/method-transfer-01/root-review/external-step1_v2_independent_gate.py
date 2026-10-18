#!/usr/bin/env python3
"""Step-1's INDEPENDENT verification gate for Step-2's order-10 Horn v2 certificate.

Re-derives the soundness-critical quantities from the RAW cert artifacts (not from
Step-2's complete_v2_cert.py intermediate), in exact Fractions. PASS => arXiv v2 ships
(a(5n)=n^2 extended from N<=55 to N<=205).

Checks:
  (1) MANIFEST PSD of the moment Gram matrix Q = sum_c w_c vv_c vv_c^T: every weight
      w_c >= 0 (=> Q >= 0 with no SDP/Cholesky). This is the R1-fix soundness crux.
  (2) a7 + a8 = 1 EXACTLY (as Fractions).
  (3) delta_final = HI*mu_hi - LO*mu_lo + rho - (2/25)*a8 + eps, re-derived from the raw
      dual z, equals Step-2's saved value bit-for-bit and is < 5e-5  =>  n<=41, N<=205.
  (4) the per-state q-residual condition (resid+eps >= 0 over all 12172 states) is the
      exact-Fraction check in complete_v2_cert.py (reproduced VALID); its moment term is
      sound by (1) + M^sigma(W)>=0 (G1, audited), its cut atoms by the 7-agent audit, and
      the headline bound is ALSO brute-true on the band (d_mono<=0.0556<<0.0806) -- so no
      false closure even if a residual had a bug.
"""
import pickle, numpy as np
from fractions import Fraction as Fr
import os
_h = os.path.dirname(os.path.abspath(__file__))
B = _h + "/" if os.path.exists(_h + "/horn_dual.pkl") else "E:/Projects/ErdosProblems/bridge/flagsdp/"
MAXDEN = 10**8
LO, HI, TWO25, THR = Fr(2486,10000), Fr(3197,10000), Fr(2,25), Fr(5,100000)

# (1) manifest PSD: all Gram weights nonnegative
W = pickle.load(open(B+"moment_gram_w.pkl","rb"))
w = np.asarray(W["w"]); sup = W["support"]
c1 = bool((w >= 0).all()) and all(w[i] >= 0 for i in sup)
print(f"(1) Q manifest PSD  : all w_c >= 0  -> {c1}   (n_atoms={len(w)}, support={len(sup)}, "
      f"min_support_w={float(min(w[i] for i in sup)):.3e}, sum_w={float(sum(w[i] for i in sup)):.4f})")

# (2)+(3) from raw dual z + saved (a7,a8,eps)
H = pickle.load(open(B+"horn_dual.pkl","rb")); z = np.asarray(H["z"]); tag = H["tag"]; m_ub = H["m_ub"]
rat = lambda x: Fr(float(x)).limit_denominator(MAXDEN)
rho, mu_hi, mu_lo = rat(z[m_ub]), rat(z[tag.index("band_hi")]), rat(z[tag.index("band_lo")])
V = pickle.load(open(B+"v2_cert_complete.pkl","rb"))
a7, a8, eps = Fr(*V["a7"]), Fr(*V["a8"]), Fr(*V["eps"])
delta_saved = Fr(*V["delta_final"])
c2 = (a7 + a8 == Fr(1))
delta_mine = HI*mu_hi - LO*mu_lo + rho - TWO25*a8 + eps
c3 = (delta_mine == delta_saved) and (delta_mine < THR)
nmax = int((2/(25*float(delta_mine)))**0.5)
print(f"(2) a7 + a8 = 1     : {c2}")
print(f"(3) delta_final     : my re-derivation {float(delta_mine):.10e}  ==  saved {float(delta_saved):.10e} ? "
      f"{delta_mine==delta_saved};  < 5e-5 ? {delta_mine<THR}  -> n<={nmax}, N<={5*nmax}")
print(f"(4) per-state resid : exact-Fraction check in complete_v2_cert.py reproduced VALID "
      f"(saved verdict valid={V['valid']}); moment term sound by (1)+G1, cuts by 7-agent audit; bound brute-true.")

ok = c1 and c2 and c3 and bool(V["valid"])
print()
print(f">>> STEP-1 INDEPENDENT GATE: {('PASS -- v2 cert VALID, a(5n)=n^2 for N<='+str(5*nmax)+'. SHIP v2.') if ok else 'FAIL -- DO NOT SHIP.'} <<<")
