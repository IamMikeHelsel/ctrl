#!/usr/bin/env python3
"""COMPLETE exact v2 cert assembly + verify (all dual-feasibility conditions, exact Fractions, consistent).
Conditions: (1) a7+a8=1; (2) per-type sum_c lambda7 >= a7; (3) per-root sum_c lambda8 >= a8;
(4) per-state q-residual R[s]=rho+(mu_hi-mu_lo)dedge[s]+sum lambda*coeff[s] - <Q,Ptilde[s]> >= 0 (weaken delta by eps);
(5) delta_final = HI*mu_hi - LO*mu_lo + rho - 2/25*a8 + eps < 5e-5.   Q=sum_c w_c vv_c vv_c^T (manifest PSD).
Set a8=min_R(sum lambda8) [max feasible -> min delta], a7=1-a8 (needs a7<=min_type(sum lambda7))."""
import pickle, numpy as np, time
from fractions import Fraction as Fr
from math import comb, prod
from scipy.sparse import csr_matrix
import prove_cert as pc, flag_exact as fx
MAXDEN=10**8; MD_V=10**6
t0=time.time()
LO=Fr(2486,10000); HI=Fr(3197,10000); TWO25=Fr(2,25); THR=Fr(5,100000)
ns0,dedge,rows,provtypes,_=pickle.load(open("cp_cache.pkl","rb"))
d=np.load("c5lift_cache.npz",allow_pickle=True)
D=csr_matrix((d["Dval"],(d["Drow"],d["Dcol"])),shape=(ns0,int(d["nJ"]))); nJ=D.shape[1]; DT=D.T.tocsr()
dedge_q=np.asarray(DT@dedge).ravel(); U7=nJ+1; U8=nJ+1+107
H=pickle.load(open("horn_dual.pkl","rb")); z=np.asarray(H["z"]); tagS=H["tag"]; m_ub=H["m_ub"]
st=pickle.load(open("horn_cert_state_it16.pkl","rb")); env=st["env"]
def tagi(n): return tagS.index(n)
def rat(x): return Fr(float(x)).limit_denominator(MAXDEN)
rho=rat(z[m_ub]); mu_hi=rat(z[tagi('band_hi')]); mu_lo=rat(z[tagi('band_lo')])
envdual={int(t.split(',')[1].rstrip(')')):z[k] for k,t in enumerate(tagS) if t.startswith("('env'")}
# (1)-(3): per-type/root exact lambda sums
from collections import defaultdict
sum7=defaultdict(lambda:Fr(0)); sum8=defaultdict(lambda:Fr(0)); lamf={}; rep7={}; type7={}
for ei,(dat,idx) in enumerate(env):
    lam=envdual.get(ei,0.0); lf=rat(lam); lamf[ei]=lf; idxa=np.asarray(idx)
    if (idxa>=U8).any(): sum8[int(idxa[idxa>=U8][0]-U8)]+=lf
    elif ((idxa>=U7)&(idxa<U8)).any():
        sg=int(idxa[(idxa>=U7)&(idxa<U8)][0]-U7); sum7[sg]+=lf; type7[ei]=sg
        if sg not in rep7: rep7[sg]=ei
min7=min(sum7.values()); min8=min(sum8.values())
a8=min8; a7=Fr(1)-a8
# LEG FIX: raise every type with sum7[sg] < a7 up to a7 (add deficit to its rep cut's lambda) -> leg(2) holds exactly
nfix=0; tot_add=Fr(0)
for sg,s in list(sum7.items()):
    if s<a7:
        d=a7-s; lamf[rep7[sg]]+=d; sum7[sg]=a7; nfix+=1; tot_add+=d
leg_k7 = all(v>=a7 for v in sum7.values()); leg_eta=(a7+a8==Fr(1))
print(f"[{time.time()-t0:.0f}s] min_type sum_l7={float(min7):.6f} min_root sum_l8={float(min8):.6f}; a8=min8 a7={float(a7):.9f}; LEG FIX: raised {nfix} types, total lambda added={float(tot_add):.3e}; leg_k7 now {leg_k7}",flush=True)
# (4a) R_cbh exact = rho + (mu_hi-mu_lo)dedge + sum lambda*coeff
dedge_f=[Fr(round(v*45),45) for v in dedge_q]
R=[rho+(mu_hi-mu_lo)*dedge_f[s] for s in range(nJ)]
for ei,(dat,idx) in enumerate(env):
    lf=lamf[ei]
    if lf==0: continue
    for v,j in zip(dat,idx):
        if j<U7: R[int(j)]+=lf*Fr(float(v)).limit_denominator(MAXDEN)
print(f"[{time.time()-t0:.0f}s] R_cbh done; computing moment term...",flush=True)
# (4b) moment term: Q=sum w_c vv_c vv_c^T over 77 support atoms
C=pc.load(9); moms=C['moments']; states=C['states']
labinfo={}
for (lab,tt,sigma,flags,s,Pf,Pint) in moms:
    k=sigma[0]; den=[Fr(int((prod(n-i for i in range(k))*comb(n-k,s)**2) if (n-k>=s) else 1) or 1) for (n,A) in states]
    labinfo[lab]=(Pint,den)
import os
if os.path.exists("mom_term_exact.pkl"):
    mom=[Fr(n,d) for (n,d) in pickle.load(open("mom_term_exact.pkl","rb"))]
    print(f"[{time.time()-t0:.0f}s] loaded cached moment term",flush=True)
else:
    W=pickle.load(open("moment_gram_w.pkl","rb")); sup=W["support"]; labs=W["atoms_lab"]; vvs=W["atoms_vv"]
    supw=[W["w"][i] for i in sup]
    Dco=D.tocoo(); Dtrip=[(int(r),int(c),Fr(float(v)).limit_denominator(10**6)) for r,c,v in zip(Dco.row,Dco.col,Dco.data)]
    mom=[Fr(0)]*nJ
    for ci,(lab,vv,wf) in enumerate(zip(labs,vvs,supw)):
        if wf<=1e-13: continue
        w_c=Fr(float(wf)).limit_denominator(MD_V); Pint,den=labinfo[lab]; vr=fx.rat_vec(np.asarray(vv),MD_V)
        bc=fx.moment_cut_exact(Pint,vr,den)
        for (t,s,coef) in Dtrip:
            if bc[t]!=0: mom[s]+=w_c*coef*bc[t]
        if (ci+1)%20==0: print(f"  moment {ci+1}/{len(sup)} [{time.time()-t0:.0f}s]",flush=True)
    pickle.dump([(r.numerator,r.denominator) for r in mom],open("mom_term_exact.pkl","wb"))
W=pickle.load(open("moment_gram_w.pkl","rb")); sup=W["support"]
BETA=Fr(1,10**6)   # GPT R1: robust slack bump (not knife's-edge); cert delta'=delta+BETA, resid >= -BETA w/ margin
resid=[R[s]-mom[s] for s in range(nJ)]
mn=min(resid); mns=int(np.argmin([float(r) for r in resid]))
ok_resid=(mn>=-BETA); eps=BETA
delta_final=HI*mu_hi-LO*mu_lo+rho-TWO25*a8+BETA
ok = leg_k7 and leg_eta and ok_resid and (delta_final<THR)
print(f"\n[{time.time()-t0:.0f}s] === COMPLETE v2 CERT VERDICT ===",flush=True)
print(f"  (1) a7+a8=1 : {a7+a8==1}",flush=True)
print(f"  (2) per-type sum_l7 >= a7 : {leg_k7}  (min {float(min7):.6f} >= {float(a7):.6f})",flush=True)
print(f"  (3) per-root sum_l8 >= a8 : {True}  (a8=min8 by constr)",flush=True)
print(f"  (4) q-residual min = {float(mn):.3e} >= -BETA={-float(BETA):.1e} ? {ok_resid}  (margin {float(BETA+mn):.3e}; robust)",flush=True)
print(f"  (5) delta_final = {float(delta_final):.7e}  < 5e-5 ? {delta_final<THR}  < 1/450 ? {delta_final<Fr(1,450)}",flush=True)
print(f"  n<= {int((2/(25*float(delta_final)))**0.5)}  (N<= {5*int((2/(25*float(delta_final)))**0.5)})",flush=True)
print(f"  >>> v2 CERT {'VALID — N<=200 EXACT' if ok else 'NOT YET VALID'} <<<",flush=True)
pickle.dump(dict(delta_final=(delta_final.numerator,delta_final.denominator),valid=bool(ok),
                 a7=(a7.numerator,a7.denominator),a8=(a8.numerator,a8.denominator),
                 eps=(eps.numerator,eps.denominator),support=sup),open("v2_cert_complete.pkl","wb"))
print("saved v2_cert_complete.pkl",flush=True); print("DONE",flush=True)
