#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "ctrl_robotics_kernels.h"

static double now_ns(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec * 1e9 + t.tv_nsec; }

int main(int argc, char **argv) {
    int n = argc > 1 ? atoi(argv[1]) : 3000, batch = 256;
    srand(0);
    const double a_cbf[3] = {-1, 0, 0};
    volatile double sink = 0;
    for (int s = 0; s < n; ++s) {
        double u_nom[3] = {1.2, 0.0, 9.81}, pi_b[3] = {-5.0, 0.0, 9.81}, u[3], f[3];
        double t0 = now_ns();
        for (int b = 0; b < batch; ++b) {
            double breq = 5.0 * rand() / RAND_MAX;          /* new state each tick */
            double lam = ctrl_lorentz_cbf_filter(a_cbf, breq, u_nom, pi_b, u);
            for (int ex = -1; ex <= 1; ex += 2)
                for (int ey = -1; ey <= 1; ey += 2) {
                    ctrl_quad_contact_force(40.0, 9.81, 0.45, 0.25, 0.18, u[0], u[1], ex, ey, f);
                    sink += f[2];
                }
            sink += lam;
        }
        printf("%.2f\n", (now_ns() - t0) / batch);
    }
    return sink == 12345.0;
}
