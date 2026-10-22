"""Classical IBVS vs depth-decoupled servoing on a 4-point planar target, 160 deg roll error."""
from __future__ import annotations
import numpy as np

S = 0.15
PTS = np.array([[S, S, 0], [-S, S, 0], [-S, -S, 0], [S, -S, 0]], float)
D0, DSTAR, PHI0, LAM = 2.2, 1.0, np.radians(160.0), 1.2
DT, TEND = 0.002, 6.0


def rot_z(a):
    c, s = np.cos(a), np.sin(a)
    return np.array([[c, -s, 0], [s, c, 0], [0, 0, 1]])


R_DOWN = np.array([[1, 0, 0], [0, -1, 0], [0, 0, -1]], float)   # camera z points to world -z


def expm_so3(w):
    th = np.linalg.norm(w)
    K = np.array([[0, -w[2], w[1]], [w[2], 0, -w[0]], [-w[1], w[0], 0]])
    if th < 1e-12:
        return np.eye(3) + K
    return np.eye(3) + np.sin(th) / th * K + (1 - np.cos(th)) / th**2 * K @ K


def features(R, p):
    Xc = (PTS - p) @ R            # rows: R^T (P - p)
    return Xc[:, :2] / Xc[:, 2:3], Xc[:, 2]


def simulate(mode):
    R = R_DOWN @ rot_z(PHI0)
    p = np.array([0.0, 0.0, D0])
    s_star, _ = features(R_DOWN, np.array([0, 0, DSTAR]))
    rows = []
    for k in range(int(TEND / DT)):
        s, Z = features(R, p)
        rows.append(dict(t=k * DT, R=R.copy(), p=p.copy(), s=s.copy(), depth=p[2]))
        if mode == "ibvs":
            L = []
            for (x, y), z in zip(s, Z):
                L += [[-1 / z, 0, x / z, x * y, -(1 + x * x), y], [0, -1 / z, y / z, 1 + y * y, -x * y, -x]]
            v = -LAM * np.linalg.pinv(np.array(L)) @ (s - s_star).ravel()
        else:
            # roll error about the optical axis and depth to the plane, handled separately
            Rerr = R_DOWN.T @ R
            theta = np.arctan2(Rerr[1, 0], Rerr[0, 0])
            depth = p[2]
            v = np.array([0, 0, LAM * (depth - DSTAR), 0, 0, -LAM * theta])
        p = p + R @ v[:3] * DT
        R = R @ expm_so3(v[3:] * DT)
    return rows, s_star


if __name__ == "__main__":
    for mode in ("ibvs", "decoupled"):
        rows, _ = simulate(mode)
        d = np.array([r["depth"] for r in rows])
        print(mode, "max depth", d.max(), "min", d.min(), "final", d[-1], "t_max", rows[int(d.argmax())]["t"])
