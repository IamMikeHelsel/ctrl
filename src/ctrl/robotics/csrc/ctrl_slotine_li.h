/* ctrl_slotine_li.h: Slotine-Li adaptive tracking kernel for the planar RR arm (C99).
 *
 * Copyright (c) 2026 Mike Helsel. Released under Apache 2.0 (see LICENSE).
 *
 * Lean source: ControlsLean/Robotics/ManipulatorTracking.lean
 *   trackingError, referenceVel, slidingError, slidingError_eq_velError_add,
 *   slotine_li_closed_loop_sliding, slotine_li_lyapunov_deriv,
 *   slotine_li_adaptive_lyapunov_deriv.
 * Geometry: ControlsLean/Robotics/PlanarArm.lean (`fk`: absolute shoulder angle q1,
 *   relative elbow angle q2, link 2 at absolute angle q1 + q2).
 *
 * The rigid-body model M, C, g and its linear parameterization are NOT in Lean;
 * PlanarArm.lean proves kinematics only. They are the standard Lagrangian model of the
 * same RR geometry in a vertical plane (gravity along -y of `fk`), parameterized by
 *   theta[0] = I1 + m1 lc1^2 + I2 + m2 (l1^2 + lc2^2)
 *   theta[1] = m2 l1 lc2
 *   theta[2] = I2 + m2 lc2^2
 *   theta[3] = m1 lc1 + m2 l1
 *   theta[4] = m2 lc2
 * so that M = [[t0 + 2 t1 c2, t2 + t1 c2], [t2 + t1 c2, t2]],
 * C = t1 s2 [[-dq2, -(dq1 + dq2)], [dq1, 0]],
 * g = g0 [t3 c1 + t4 c12, t4 c12].
 * A point payload m_p at the tip adds m_p (l1^2 + l2^2, l1 l2, l2^2, l1, l2).
 *
 * All arrays are row-major. No heap allocation, no global state, reentrant.
 */
#ifndef CTRL_SLOTINE_LI_H
#define CTRL_SLOTINE_LI_H

#ifdef __cplusplus
extern "C" {
#endif

#define CTRL_RR_NQ 2
#define CTRL_RR_NP 5

/* Regressor Y (2x5, row-major) with Y theta = M(q) a + C(q, dq) v + g(q). */
void ctrl_planar_rr_regressor(const double q[2], const double dq[2], const double v[2],
                              const double a[2], double g0, double Y[10]);

/* Slotine-Li adaptive law. Inputs: state q, dq; desired q_d, dq_d, ddq_d; gains
 * Lambda (2x2), Kd (2x2), Gamma (5x5); estimate theta_hat (5); gravity g0.
 * Outputs (any pointer except tau may be NULL):
 *   tau        = Y theta_hat - Kd s
 *   theta_dot  = -Gamma Y^T s
 *   s          = (dq - dq_d) + Lambda (q - q_d)
 *   dq_r       = dq_d - Lambda (q - q_d)
 *   ddq_r      = ddq_d - Lambda (dq - dq_d)
 *   Y          = regressor at (q, dq, dq_r, ddq_r)
 * Returns 0 on success, -1 if a required pointer is NULL. */
int ctrl_slotine_li_torque(const double q[2], const double dq[2], const double q_d[2],
                           const double dq_d[2], const double ddq_d[2],
                           const double Lambda[4], const double Kd[4],
                           const double Gamma[25], const double theta_hat[5], double g0,
                           double tau[2], double theta_dot[5], double s[2],
                           double dq_r[2], double ddq_r[2], double Y[10]);

#ifdef __cplusplus
}
#endif

#endif /* CTRL_SLOTINE_LI_H */
