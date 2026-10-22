"""Time a 12-variable SOCP force allocation (4 Lorentz cones) with Clarabel over random states."""
import json, sys, time
import numpy as np
import clarabel
from scipy import sparse

m, g, h, wx, wy, mu = 40.0, 9.81, 0.45, 0.25, 0.18, 0.6
corners = [(1, 1), (1, -1), (-1, 1), (-1, -1)]
rng = np.random.default_rng(0)

# Variables f = [f1x f1y f1z ... f4x f4y f4z]. Equality: sum f = m(a + g e_z); sum r x f = 0.
A_eq = np.zeros((6, 12))
for i, (ex, ey) in enumerate(corners):
    r = np.array([ex * wx, ey * wy, -h])
    A_eq[0:3, 3 * i:3 * i + 3] = np.eye(3)
    rx = np.array([[0, -r[2], r[1]], [r[2], 0, -r[0]], [-r[1], r[0], 0]])
    A_eq[3:6, 3 * i:3 * i + 3] = rx
# Cone rows: for each foot, (mu fz, fx, fy) in SOC  ->  s = b - A f, with A rows -[mu*fz, fx, fy]
A_soc = np.zeros((12, 12))
for i in range(4):
    A_soc[3 * i, 3 * i + 2] = -mu
    A_soc[3 * i + 1, 3 * i + 0] = -1
    A_soc[3 * i + 2, 3 * i + 1] = -1
P = sparse.csc_matrix(np.eye(12) * 1e-3)   # least-norm force distribution
A = sparse.csc_matrix(np.vstack([A_eq, A_soc]))
cones = [clarabel.ZeroConeT(6)] + [clarabel.SecondOrderConeT(3)] * 4
settings = clarabel.DefaultSettings()
settings.verbose = False

times, iters, status = [], [], []
N = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
a_max = min(mu, wx / h) * g
for _ in range(N):
    th = rng.uniform(0, 2 * np.pi)
    mag = a_max * rng.uniform(0.0, 0.98)
    ax, ay = mag * np.cos(th), mag * np.sin(th) * (wy / wx)
    b = np.concatenate([[m * ax, m * ay, m * g, 0, 0, 0], np.zeros(12)])
    solver = clarabel.DefaultSolver(P, np.zeros(12), A, b, cones, settings)
    t0 = time.perf_counter_ns()
    sol = solver.solve()
    wall = time.perf_counter_ns() - t0
    times.append(wall)
    iters.append(sol.iterations)
    status.append(str(sol.status))
print(json.dumps(dict(ns=times, iters=iters, solved=sum(s == "Solved" for s in status), n=N)))
