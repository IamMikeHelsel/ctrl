"""Second n=6 ascent batch: starts near the full-rank ascent limits (perturbation scale 0.05-0.5),
near the pod's SS-fail matrix, and near adversarial span-ratio minimisers."""
import os; os.environ.setdefault('OMP_NUM_THREADS','1')
import numpy as np, json, sys, time
from fractions import Fraction as Fr
from multiprocessing import Pool
from gauge import ascent
from core import bases, op_mats, top_pair
D=os.path.dirname(os.path.abspath(__file__))
A1=json.load(open(f'{D}/ascent_n6_0.json'))
FR=[np.array(o['A']) for o in sorted(A1,key=lambda o:-o['svK'][4])[:10]]
SSF=np.array([[float(Fr(x)) for x in r] for r in json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'cert_ss_fail.json')))['A_num']])
ADV=[np.array(o['A']) for o in json.load(open(f'{D}/adv_bd.json'))]
def job(seed):
    rng=np.random.default_rng(555+seed)
    st=seed%3; sc=[0.05,0.15,0.3,0.5][(seed//3)%4]
    base={0:FR[seed%len(FR)],1:SSF/np.linalg.norm(SSF),2:ADV[seed%len(ADV)]}[st]
    A=base/np.linalg.norm(base)+sc*rng.standard_normal((6,6))/6
    t=time.time(); A2,r,h=ascent(A,iters=25)
    S,Kb=bases(6); LS,LK=op_mats(A2); k,Y,K,sv=top_pair(LK,Kb)
    return dict(seed=seed,kind=['fullrank_lim','ssfail','advBD'][st]+f'_{sc}',ratio=r,r0=h[0][0],iters=len(h),
                svK=np.linalg.svd(K,compute_uv=False).tolist(),A=A2.tolist())
if __name__=='__main__':
    N=int(sys.argv[1]); out=[]
    with Pool(4) as p:
        for res in p.imap_unordered(job,range(N)):
            out.append(res)
            print(f"{res['seed']:4d} {res['kind']:18s} r0={res['r0']:.9f} r={res['ratio']:.12f} it={res['iters']} svK={np.round(res['svK'],3)}",flush=True)
            json.dump(out,open(f'{D}/ascent_n6_b.json','w'))
    rs=[o['ratio'] for o in out]; print('MAX',max(rs),'#>1+1e-9',sum(r>1+1e-9 for r in rs))
