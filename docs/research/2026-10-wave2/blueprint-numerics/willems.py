import numpy as np
rng=np.random.default_rng(1)
def hank(w,L,N): return np.vstack([np.hstack([w[j+i][:,None] for j in range(N)]) for i in range(L)])
ok=0;tot=0
for trial in range(300):
    n=rng.integers(1,5); m=rng.integers(1,3); p=rng.integers(1,3); L=rng.integers(1,5)
    A=rng.normal(size=(n,n)); B=rng.normal(size=(n,m)); C=rng.normal(size=(p,n)); D=rng.normal(size=(p,m))
    if trial%3==0: A=np.zeros((n,n)); A[0,0]=1  # possibly uncontrollable
    ctrb=np.hstack([np.linalg.matrix_power(A,k)@B for k in range(n)])
    controllable=np.linalg.matrix_rank(ctrb)==n
    T=(m+1)*(L+n)-1+rng.integers(0,3)
    u=[rng.normal(size=m) for _ in range(T)]
    if trial%5==0: u=[np.ones(m) for _ in range(T)]   # not PE
    x=[rng.normal(size=n)]
    for k in range(T): x.append(A@x[-1]+B@u[k])
    y=[C@x[k]+D@u[k] for k in range(T)]
    N=T-L-n+1
    PE=np.linalg.matrix_rank(hank(u,L+n,N))==m*(L+n)
    Ncol=T-L+1
    M=np.vstack([np.hstack([x[j][:,None] for j in range(Ncol)]), hank(u,L,Ncol)])
    full=np.linalg.matrix_rank(M)==n+m*L
    if controllable and PE:
        tot+=1; ok+=full
        H=np.vstack([hank(u,L,Ncol),hank(y,L,Ncol)])
        # random trajectory in column span?
        x0=rng.normal(size=n); ub=[rng.normal(size=m) for _ in range(L)]; xs=[x0]; yb=[]
        for k in range(L): yb.append(C@xs[-1]+D@ub[k]); xs.append(A@xs[-1]+B@ub[k])
        w=np.concatenate([np.concatenate(ub),np.concatenate(yb)])
        g=np.linalg.lstsq(H,w,rcond=None)[0]; assert np.linalg.norm(H@g-w)<1e-6, "not in span"
print("controllable&PE cases:",tot,"full rank [X;H_L(u)] in",ok)
