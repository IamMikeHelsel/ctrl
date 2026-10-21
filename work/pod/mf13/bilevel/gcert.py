"""Rayleigh-quotient certificate:  g(K,Y) = max { -(<Z1,Y>+<Z2,K>) : M = Z1 K + Y Z2 symmetric PSD, tr M = 1 }.
Then for every A with pair (K,Y) value 1:  sup_X <X,L_A X>/|X|^2 >= g, hence ||L_A|S|| >= g.
Also numerically-verified identity: 2 tr(A M) = -(<Z1,Y>+<Z2,K>)."""
import numpy as np
import cvxpy as cp
from n6 import *


def g_cert(K, Y, return_sol=False):
    Z1 = cp.Variable((6, 6)); Z2 = cp.Variable((6, 6))
    M = Z1 @ K + Y @ Z2
    cons = [Z1 + Z1.T == 0, Z2 + Z2.T == 0, M == M.T, M >> 0, cp.trace(M) == 1]
    obj = -(cp.sum(cp.multiply(Z1, Y)) + cp.sum(cp.multiply(Z2, K)))
    prob = cp.Problem(cp.Maximize(obj - 1e-7*(cp.sum_squares(Z1)+cp.sum_squares(Z2))), cons)
    prob.solve(solver=cp.CLARABEL)
    if return_sol:
        return prob.value, Z1.value, Z2.value, M.value
    return prob.value
