"""n=6 (and control n=7) monotone SDP ascent from diverse starts, incl. deflation of the n=7 optimum."""
import os
os.environ.setdefault('OMP_NUM_THREADS','1')
import numpy as np, json, sys, time
from multiprocessing import Pool
from gauge import ascent, Gauge, top_skew_P
from core import rand_A, s_k, bases, op_mats, top_pair

D=os.path.dirname(os.path.abspath(__file__))
A7=np.array(json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'cert_n7.json')))['A'],float)

def start(n,seed):
    rng=np.random.default_rng(10000+seed)
    kinds=['gauss','sparse','nilp','cauchy','lowrank','defl_rand','defl_K','defl_Y']
    kind=kinds[seed%len(kinds)]
    if kind.startswith('defl') and n==6:
        # compress the n=7 counterexample onto a 6-dim subspace
        A=A7/np.linalg.norm(A7)
        P,K,Y=top_skew_P(A)
        if kind=='defl_rand':
            Q=np.linalg.qr(rng.standard_normal((7,6)))[0]
        else:
            M=K if kind=='defl_K' else Y
            w,V=np.linalg.eigh(M.T@M)  # kernel = smallest
            ker=V[:,0]
            ker=ker+0.3*rng.random()*rng.standard_normal(7); ker/=np.linalg.norm(ker)
            Q=np.linalg.svd(np.eye(7)-np.outer(ker,ker))[0][:,:6]
        A6=Q.T@A@Q
        return kind, A6+0.02*rng.random()*rng.standard_normal((6,6))
    if kind.startswith('defl'): kind='gauss'
    return kind, rand_A(n,rng,kind)

def job(args):
    n,seed,iters=args
    kind,A=start(n,seed)
    t=time.time()
    A2,r,h=ascent(A,iters=iters)
    S,Kb=bases(n); LS,LK=op_mats(A2)
    k,Y,K,sv=top_pair(LK,Kb)
    sk=np.linalg.svd(K,compute_uv=False)
    return dict(seed=seed,kind=kind,ratio=r,r0=h[0][0],iters=len(h),time=time.time()-t,
                svK=sk.tolist(),A=A2.tolist())

if __name__=='__main__':
    n=int(sys.argv[1]); N=int(sys.argv[2]); iters=int(sys.argv[3]); off=int(sys.argv[4]) if len(sys.argv)>4 else 0
    out=[]
    with Pool(4) as p:
        for res in p.imap_unordered(job,[(n,off+i,iters) for i in range(N)]):
            out.append(res)
            print(f"{res['seed']:5d} {res['kind']:10s} r0={res['r0']:.9f} r={res['ratio']:.12f} it={res['iters']} t={res['time']:.0f} svK={np.round(res['svK'],3)}",flush=True)
            json.dump(out,open(f'{D}/ascent_n{n}_{off}.json','w'))
    rs=[o['ratio'] for o in out]
    print('MAX',max(rs),'#>1+1e-9',sum(r>1+1e-9 for r in rs))
