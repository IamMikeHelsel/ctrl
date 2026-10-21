import sys, json
import numpy as np
fn = sys.argv[1]
sys.argv = ['x', '7', '1', '0.02', '1']
import track_a_gen as T
from bl import *
from barrier import barrier_min_sigma
np.set_printoptions(precision=5, suppress=True, linewidth=170)
d = json.load(open(fn)); x = np.array(d['x'])
K, Y, err = T.build(x)
A0, Ar, resid, rank = affine_family(K, Y)
B0 = BS(A0); Br = np.array([BS(a) for a in Ar])
fv, z, t, nit = barrier_min_sigma(B0, Br, tol=1e-13)
A = A0 + np.tensordot(z, Ar, axes=(0, 0))
Sb, Kb = bases(7)
u, s, vt = np.linalg.svd(BS(A))
print("f", fv, " top sym sv", s[:8])
for j in range(3):
    Xv = np.tensordot(vt[j], Sb, axes=(0, 0)); Xu = np.tensordot(u[:, j], Sb, axes=(0, 0))
    print(f" j={j}: Xv eig {np.linalg.eigvalsh(Xv)}  |Xv^2+K^2|={np.linalg.norm(Xv@Xv+K@K):.3f} |XK+KX|={np.linalg.norm(Xv@K+K@Xv):.3f} | Xu: |Xu^2+Y^2|={np.linalg.norm(Xu@Xu+Y@Y):.3f}")
print("eig(YK)", np.sort_complex(np.linalg.eigvals(Y @ K)))
print("A* eig", np.sort_complex(np.linalg.eigvals(A)))
# kernels
uK = np.linalg.svd(K)[0][:, -1]; uY = np.linalg.svd(Y)[0][:, -1]
print("cos(ker K, ker Y) =", abs(uK @ uY))
