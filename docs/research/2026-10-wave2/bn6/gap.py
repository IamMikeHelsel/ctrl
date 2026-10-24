"""Diagnostics for the ctrl 'J vs {I2,F,G} cross-term' gap (step 5).

For A in R^{6x6}: K = top skew right singular vector of L_A, put in Darboux frame
K = diag(aJ,bJ,cJ) (orthogonal change of frame; L is equivariant). Y = L_A K, H = (AK - KA^T)/2.
Quantities:
  c8      = max over the 8 Lean comparators K T_r, K G_r of ||L_A S||^2 / ||Y||^2   (||S|| = ||K||)
  cSS     = max over the full same-square class {S sym : S^2 = -K^2} (27 components: per plane +aI, -aI, a*refl(theta))
  cBD     = s_BD^2 / k^2 where s_BD = ||L_A restricted to block-diagonal Sym (9-dim)|| -- the linear span
            of every comparator the Lean modules use (all their involutions are block-diagonal in this frame).
            Any pairing argument sum <U_r, L_A V_r> with V_r in this span proves at most k <= s_BD.
  lean8   = (4||H||^2 + 4||iso H||^2) / ||Y_off||^2   (Lean dominance criterion holds iff >= 1)
  regime  = (1/2)||Y_off||^2 / ((3/4)||Y_diag||^2)   (the caller's 'gap regime' is regime > 1)
  Jfrac   = ||J components of off-diagonal blocks||^2 / ||Y_off||^2
"""
import numpy as np
from core import bases, op_mats, top_pair, darboux, lyap
J=np.array([[0,1.],[-1,0]]); F=np.array([[1,0.],[0,-1]]); Gm=np.array([[0,1.],[1,0]]); I2=np.eye(2)

def blkdiag(*bs):
    n=sum(b.shape[0] for b in bs); M=np.zeros((n,n)); i=0
    for b in bs: k=b.shape[0]; M[i:i+k,i:i+k]=b; i+=k
    return M

def lean_involutions():
    Ts=[blkdiag(F,F,F),blkdiag(F,-F,-F),blkdiag(-F,F,-F),blkdiag(-F,-F,F)]
    Gs=[blkdiag(Gm,Gm,Gm),blkdiag(Gm,-Gm,-Gm),blkdiag(-Gm,Gm,-Gm),blkdiag(-Gm,-Gm,Gm)]
    return Ts+Gs

def refl(t): return np.array([[np.cos(t),np.sin(t)],[np.sin(t),-np.cos(t)]])

def frame(A):
    n=A.shape[0]; S,Kb=bases(n); LS,LK=op_mats(A)
    k,Y,K,sv=top_pair(LK,Kb)
    Q,fr=darboux(K)
    A1=Q@A@Q.T; K1=Q@K@Q.T
    K1=np.where(abs(K1)<1e-13,0,K1)
    return A1,K1,fr,k,sv

BD_basis=None
def bd_basis():
    global BD_basis
    if BD_basis is None:
        B=[]
        for p in range(3):
            for E in [np.diag([1.,0]),np.diag([0,1.]),Gm/np.sqrt(2)]:
                M=np.zeros((6,6)); M[2*p:2*p+2,2*p:2*p+2]=E; B.append(M)
        BD_basis=np.array(B)
    return BD_basis

def s_restricted(A,B):
    imgs=np.array([lyap(A,b) for b in B]).reshape(len(B),-1)
    return np.linalg.norm(imgs,2)

def same_square_max(A,K,fr,ngrid=12):
    """max ||L_A S||^2 over S with S^2=-K^2, blockwise S_p in {+f I, -f I, f*refl(theta)}"""
    from scipy.optimize import minimize
    best=-1
    opts=['+','-','R']
    th=np.linspace(0,2*np.pi,ngrid,endpoint=False)
    def build(c,t):
        bl=[]
        for p in range(3):
            if c[p]=='+': bl.append(fr[p]*I2)
            elif c[p]=='-': bl.append(-fr[p]*I2)
            else: bl.append(fr[p]*refl(t[p]))
        return blkdiag(*bl)
    for c0 in opts:
        for c1 in opts:
            for c2 in opts:
                c=(c0,c1,c2); idx=[p for p in range(3) if c[p]=='R']
                f=lambda t: -np.sum(lyap(A,build(c,t))**2)
                grids=np.array(np.meshgrid(*([th]*len(idx)))).reshape(len(idx),-1).T if idx else [np.zeros(0)]
                vals=[]
                for g in grids:
                    t=np.zeros(3); t[idx]=g; vals.append((f(t),t))
                vals.sort(key=lambda z:z[0])
                for v,t in vals[:3]:
                    if idx:
                        r=minimize(lambda x: f(np.put(t,idx,x) or t), t[idx], method='BFGS')
                        v=r.fun
                    best=max(best,-v)
    return best

def diagnostics(A, full=True):
    A1,K1,fr,k,sv=frame(A)
    Y=lyap(A1,K1); H=0.5*(A1@K1-K1@A1.T)
    nY=np.sum(Y**2); nK=np.sum(K1**2)
    Yd=np.zeros_like(Y); 
    for p in range(3): Yd[2*p:2*p+2,2*p:2*p+2]=Y[2*p:2*p+2,2*p:2*p+2]
    Yo=Y-Yd
    iso=np.diag(np.repeat([(H[2*p,2*p]+H[2*p+1,2*p+1])/2 for p in range(3)],2))
    Jn=0
    for p in range(3):
        for q in range(p+1,3):
            M=Y[2*p:2*p+2,2*q:2*q+2]; Jn+=2*(np.sum(M*J)/2)**2*2  # J-coeff delta=<M,J>/2; ||delta J||^2=2delta^2; both blocks
    c8=max(np.sum(lyap(A1,K1@T)**2) for T in lean_involutions())/nY
    sBD=s_restricted(A1,bd_basis())
    out=dict(k=k, gap_k2_over_k1=sv[1]/sv[0], freqs=fr.tolist(), c8=c8, cBD=sBD**2*nK/nY,
             lean8=(4*np.sum(H**2)+4*np.sum(iso**2))/np.sum(Yo**2), regime=0.5*np.sum(Yo**2)/(0.75*np.sum(Yd**2)),
             Jfrac=Jn/np.sum(Yo**2))
    if full: out['cSS']=same_square_max(A1,K1,fr)/nY
    return out

if __name__=='__main__':
    rng=np.random.default_rng(0)
    # identity checks (Lean statement vs STATUS doc statement)
    A=rng.standard_normal((6,6)); a,b,c=1.3,0.7,0.4
    K=blkdiag(a*J,b*J,c*J); Y=lyap(A,K); H=0.5*(A@K-K@A.T)
    Yd=np.zeros_like(Y)
    for p in range(3): Yd[2*p:2*p+2,2*p:2*p+2]=Y[2*p:2*p+2,2*p:2*p+2]
    Yo=Y-Yd; iso=np.diag(np.repeat([(H[2*p,2*p]+H[2*p+1,2*p+1])/2 for p in range(3)],2))
    lhs=sum(np.sum(lyap(A,K@T)**2) for T in lean_involutions())
    lean=16*np.sum(H**2)+16*np.sum(iso**2)+4*np.sum(Y**2)+4*np.sum(Yd**2)
    status=8*np.sum(Y**2)-6*np.sum(Yd**2)+2*np.sum(Yo**2)
    print('8-involution sum',lhs,' Lean RHS',lean,' STATUS-doc RHS',status)
    T=lean_involutions()[1]; Hc=0.5*(H+T@H@T); Ya=0.5*(Y-T@Y@T)
    print('I2 check',np.sum(lyap(A,K@T)**2), 4*np.sum(Hc**2)+np.sum(Ya**2))
    for i in range(3):
        print(diagnostics(rng.standard_normal((6,6))))

def sub_bases():
    T6=[];S3=[]
    for p in range(3):
        for E in [F/np.sqrt(2),Gm/np.sqrt(2)]:
            M=np.zeros((6,6)); M[2*p:2*p+2,2*p:2*p+2]=E; T6.append(M)
        M=np.zeros((6,6)); M[2*p:2*p+2,2*p:2*p+2]=I2/np.sqrt(2); S3.append(M)
    return np.array(T6),np.array(S3)

def span_ratios(A):
    """(cT6, cS3, cBD): restricted s^2/k^2 on traceless block-diag (=span of torus comparators KT),
    scalar block-diag, and full block-diag symmetric, in the Darboux frame of the top skew K."""
    A1,K1,fr,k,sv=frame(A)
    T6,S3=sub_bases()
    return tuple((s_restricted(A1,B)/k)**2 for B in (T6,S3,bd_basis()))
