import json, numpy as np
from ridge_solve import *
from fss import canon_frame
d = json.load(open('runs/A_s2_e0.05.best.json')); x = np.array(d['x'])
w = abc_from_uv(x[0], x[1]); K = make_K(*w)
Y, err = Y_from_x(K, x[2:])
out = f_of_pair(K, Y, tol=1e-12, want_z=True)
u, s, vt = np.linalg.svd(BS(out['A']))
Sb, Kb_ = bases(6)
Xv = np.tensordot(vt[0], Sb, axes=(0,0)); Xu = np.tensordot(u[:,0], Sb, axes=(0,0))
print("moments", moments(K,Y), "|Y|", np.linalg.norm(Y))
cols = [(B @ K).ravel() for B in Kb] + [(Y @ B).ravel() for B in Kb]
Mat = np.array(cols).T
uu, ss, vv = np.linalg.svd(Mat, full_matrices=False)
print("sv Mat", ss[-6:], "rank", (ss>1e-9*ss[0]).sum())
U = uu[:, ss > 1e-9*ss[0]]
p = (Xu@Xv).ravel(); print("true Xu Xv resid", np.linalg.norm(p - U@(U.T@p)))
wK = np.array([K[0, 1], K[2, 3], K[4, 5]])
th = np.array([np.arctan2(Xv[2*i, 2*i+1] / wK[i], Xv[2*i, 2*i] / wK[i]) for i in range(3)])
FY, wY = canon_frame(Y)
Xu_c = FY.T @ Xu @ FY
ph = np.array([np.arctan2(Xu_c[2*i, 2*i+1] / wY[i], Xu_c[2*i, 2*i] / wY[i]) for i in range(3)])
Xu2, Xv2 = Xs(K, Y, th, ph)
print("Xv err", np.linalg.norm(Xv2-Xv), np.linalg.norm(Xv2+Xv), "Xu err", np.linalg.norm(Xu2-Xu), np.linalg.norm(Xu2+Xu))
p2 = (Xu2@Xv2).ravel(); print("resid recon", np.linalg.norm(p2 - U@(U.T@p2)))
x0 = np.concatenate([vec_from_skew(Y), th, ph])
print("resid()", np.linalg.norm(resid(x0, K)), "m part", np.linalg.norm(resid(x0,K)[:3]))
print("diff y", np.linalg.norm(skew_from_vec(x0[:15]) - Y))
print("----")
y = x0[:15]; Y3 = skew_from_vec(y)
print("Y3 vs Y", np.linalg.norm(Y3-Y))
Xu3, Xv3 = Xs(K, Y3, th, ph)
print("Xu3 vs Xu2", np.linalg.norm(Xu3-Xu2), np.linalg.norm(Xv3-Xv2))
cols3 = [(B @ K).ravel() for B in Kb] + [(Y3 @ B).ravel() for B in Kb]
Mat3 = np.array(cols3).T
print("Mat3 vs Mat", np.linalg.norm(Mat3-Mat))
print("----")
y = x0[:15]; Y3 = skew_from_vec(y)
print("Y3 vs Y", np.linalg.norm(Y3-Y))
Xu3, Xv3 = Xs(K, Y3, th, ph)
print("Xu3 vs Xu2", np.linalg.norm(Xu3-Xu2), np.linalg.norm(Xv3-Xv2))
cols3 = [(B @ K).ravel() for B in Kb] + [(Y3 @ B).ravel() for B in Kb]
Mat3 = np.array(cols3).T
print("Mat3 vs Mat", np.linalg.norm(Mat3-Mat))
