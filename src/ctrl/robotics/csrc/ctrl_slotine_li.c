/* ctrl_slotine_li.c: Slotine-Li adaptive tracking kernel for the planar RR arm (C99).
 *
 * Copyright (c) 2026 Mike Helsel. Released under Apache 2.0 (see LICENSE).
 * See ctrl_slotine_li.h for the model, the parameterization and what is (and is not)
 * covered by Lean. Fixed-size loops, stack scratch only, no heap allocation.
 */
#include "ctrl_slotine_li.h"

#include <math.h>
#include <stddef.h>

void ctrl_planar_rr_regressor(const double q[2], const double dq[2], const double v[2],
                              const double a[2], double g0, double Y[10]) {
    const double c1 = cos(q[0]);
    const double c2 = cos(q[1]);
    const double s2 = sin(q[1]);
    const double c12 = cos(q[0] + q[1]);

    /* Row 0: (M a + C v + g)_0 */
    Y[0] = a[0];
    Y[1] = c2 * (2.0 * a[0] + a[1]) - s2 * (dq[1] * v[0] + (dq[0] + dq[1]) * v[1]);
    Y[2] = a[1];
    Y[3] = g0 * c1;
    Y[4] = g0 * c12;
    /* Row 1: (M a + C v + g)_1 */
    Y[5] = 0.0;
    Y[6] = c2 * a[0] + s2 * dq[0] * v[0];
    Y[7] = a[0] + a[1];
    Y[8] = 0.0;
    Y[9] = g0 * c12;
}

int ctrl_slotine_li_torque(const double q[2], const double dq[2], const double q_d[2],
                           const double dq_d[2], const double ddq_d[2],
                           const double Lambda[4], const double Kd[4],
                           const double Gamma[25], const double theta_hat[5], double g0,
                           double tau[2], double theta_dot[5], double s[2],
                           double dq_r[2], double ddq_r[2], double Y[10]) {
    double e[2], de[2], sl[2], vr[2], ar[2], Yl[10], ys[5];
    int i, j;

    if (q == NULL || dq == NULL || q_d == NULL || dq_d == NULL || ddq_d == NULL ||
        Lambda == NULL || Kd == NULL || theta_hat == NULL || tau == NULL) {
        return -1;
    }
    if (theta_dot != NULL && Gamma == NULL) {
        return -1;
    }

    /* Lean `trackingError`: q~ = q - q_d; velocity error dq - dq_d. */
    for (i = 0; i < 2; ++i) {
        e[i] = q[i] - q_d[i];
        de[i] = dq[i] - dq_d[i];
    }
    /* Lean `referenceVel`: dq_r = dq_d - Lambda q~.
     * Its time derivative with constant Lambda: ddq_r = ddq_d - Lambda (dq - dq_d).
     * Lean `slidingError`: s = dq - dq_r, which equals (dq - dq_d) + Lambda q~
     * by `slidingError_eq_velError_add`. */
    for (i = 0; i < 2; ++i) {
        vr[i] = dq_d[i] - (Lambda[2 * i] * e[0] + Lambda[2 * i + 1] * e[1]);
        ar[i] = ddq_d[i] - (Lambda[2 * i] * de[0] + Lambda[2 * i + 1] * de[1]);
        sl[i] = dq[i] - vr[i];
    }

    ctrl_planar_rr_regressor(q, dq, vr, ar, g0, Yl);

    /* tau = Y theta_hat - Kd s. With Y theta = M ddq_r + C dq_r + g this is Lean
     * `slotineLiControl` evaluated at the estimate, and for the true plant the closed
     * loop is M ds + C s + Kd s = Y (theta_hat - theta), the `hcl` hypothesis of
     * `slotine_li_adaptive_lyapunov_deriv` (with theta_hat = theta it is the
     * `slotine_li_closed_loop_sliding` conclusion used by `slotine_li_lyapunov_deriv`). */
    for (i = 0; i < 2; ++i) {
        double acc = 0.0;
        for (j = 0; j < 5; ++j) {
            acc += Yl[5 * i + j] * theta_hat[j];
        }
        tau[i] = acc - (Kd[2 * i] * sl[0] + Kd[2 * i + 1] * sl[1]);
    }

    /* Adaptation theta_hat_dot = -Gamma Y^T s. The true theta is constant, so
     * theta~_dot = theta_hat_dot and Gamma^{-1} theta~_dot = -Y^T s, which is the
     * `hadapt` hypothesis of `slotine_li_adaptive_lyapunov_deriv`. */
    if (theta_dot != NULL) {
        for (j = 0; j < 5; ++j) {
            ys[j] = Yl[j] * sl[0] + Yl[5 + j] * sl[1];
        }
        for (i = 0; i < 5; ++i) {
            double acc = 0.0;
            for (j = 0; j < 5; ++j) {
                acc += Gamma[5 * i + j] * ys[j];
            }
            theta_dot[i] = -acc;
        }
    }

    if (s != NULL) {
        s[0] = sl[0];
        s[1] = sl[1];
    }
    if (dq_r != NULL) {
        dq_r[0] = vr[0];
        dq_r[1] = vr[1];
    }
    if (ddq_r != NULL) {
        ddq_r[0] = ar[0];
        ddq_r[1] = ar[1];
    }
    if (Y != NULL) {
        for (j = 0; j < 10; ++j) {
            Y[j] = Yl[j];
        }
    }
    return 0;
}
