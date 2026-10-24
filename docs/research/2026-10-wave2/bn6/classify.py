"""Classify ascent limits: rank of K, common-T defect (min over symmetric involutions T anticommuting with K
of ||TYT+Y||/||Y||, searched over block reflections in the Darboux frame; exact for distinct frequencies)."""
import numpy as np, json, sys
from scipy.optimize import minimize
from gap import frame, refl, blkdiag, diagnostics
from core import lyap, bases, op_mats, top_pair

def commonT_defect(A):
    A1,K1,fr,k,sv=frame(A)
    Y=lyap(A1,K1)
    # left singular vector Y ~ L_A K (normalised)
    def d(t):
        T=blkdiag(refl(t[0]),refl(t[1]),refl(t[2]))
        return np.linalg.norm(T@Y@T+Y)/np.linalg.norm(Y)
    best=9
    for g in np.random.default_rng(0).uniform(0,2*np.pi,(60,3)):
        r=minimize(d,g,method='BFGS'); best=min(best,r.fun)
    return best,fr

if __name__=='__main__':
    out=json.load(open(sys.argv[1]))
    out.sort(key=lambda o:-o['ratio'])
    for o in out[:int(sys.argv[2]) if len(sys.argv)>2 else 30]:
        A=np.array(o['A']); dft,fr=commonT_defect(A)
        dg=diagnostics(A,full=False)
        print(f"{o['seed']:4d} {o['kind']:9s} r={o['ratio']:.12f} freqs={np.round(fr,4)} commonT_defect={dft:.2e} cBD={dg['cBD']:.6f} c8={dg['c8']:.4f} k2/k1={dg['gap_k2_over_k1']:.6f}")
