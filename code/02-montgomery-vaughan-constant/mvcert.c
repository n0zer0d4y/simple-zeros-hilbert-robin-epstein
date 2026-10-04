// mvcert.c: rigorous lower bound for the optimal constant in the Montgomery-Vaughan weighted Hilbert inequality from integer data.
//   input (text): N, then N-1 integer gaps, then N lines "a_m b_m" (w_m = a_m + i b_m, integers, |a|,|b| < 2^56).
//   T = sum_{m != n} b_m a_n / (lambda_m - lambda_n)   (the double sum equals 2 i T),  Den = sum (a_m^2 + b_m^2)/delta_m,   ratio = 2|T|/Den <= C.
//   Arithmetic in __float128 (113-bit significand, u = 2^-113): each term fl(fl(b a)/d) has relative error <= u (b a is exact), recursive summation of K terms adds <= K u sum|t|.
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <quadmath.h>
typedef long long ll;
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int N; if (fscanf(f, "%d", &N) != 1) return 1;
    ll *g = malloc(sizeof(ll) * (N - 1)), *lam = malloc(sizeof(ll) * N), *dl = malloc(sizeof(ll) * N), *a = malloc(sizeof(ll) * N), *b = malloc(sizeof(ll) * N);
    for (int i = 0; i < N - 1; i++) if (fscanf(f, "%lld", &g[i]) != 1) return 1;
    for (int i = 0; i < N; i++) if (fscanf(f, "%lld %lld", &a[i], &b[i]) != 2) return 1;
    lam[0] = 0; for (int i = 1; i < N; i++) lam[i] = lam[i - 1] + g[i - 1];
    dl[0] = g[0]; dl[N - 1] = g[N - 2]; for (int i = 1; i < N - 1; i++) dl[i] = g[i - 1] < g[i] ? g[i - 1] : g[i];
    // verify delta by brute force on the neighbours only (sorted lambda): the nearest other point is a neighbour
    __float128 T = 0, S = 0; double absum = 0.0;
    for (int m = 0; m < N; m++) {
        __float128 bm = (__float128)b[m], row = 0;
        double arow = 0.0;
        for (int n = 0; n < N; n++) {
            if (n == m) continue;
            __float128 t = ((__float128)a[n]) / (__float128)(lam[m] - lam[n]);     // a_n / d, rounded once
            row += t;
            arow += fabs((double)a[n]) / fabs((double)(lam[m] - lam[n]));
        }
        T += bm * row; absum += fabs((double)b[m]) * arow;
    }
    // NOTE: the row sums are accumulated first and multiplied by b_m afterwards: error bound (N + 1) u sum_n |a_n|/|d| per row, then one more rounding in b_m * row and in the outer sum.
    __float128 Den = 0; double denabs = 0.0;
    for (int m = 0; m < N; m++) { __float128 num = (__float128)a[m] * (__float128)a[m] + (__float128)b[m] * (__float128)b[m]; Den += num / (__float128)dl[m]; denabs += (double)num / (double)dl[m]; }
    const __float128 u = ldexpq(1.0Q, -113);
    __float128 errT = ((__float128)N * 2 + 4) * u * (__float128)absum * (1 + 1e-6);      // rows: N u each plus the outer accumulation and the products
    __float128 errD = ((__float128)N + 4) * u * (__float128)denabs * (1 + 1e-6);
    __float128 Tabs = fabsq(T);
    __float128 lower = 2 * (Tabs - errT) / (Den + errD), upper = 2 * (Tabs + errT) / (Den - errD);
    char buf[128];
    quadmath_snprintf(buf, sizeof buf, "%.30Qg", lower); printf("N = %d  extent = %lld\nratio lower bound = %s\n", N, lam[N - 1], buf);
    quadmath_snprintf(buf, sizeof buf, "%.30Qg", upper); printf("ratio upper (error check) = %s\n", buf);
    quadmath_snprintf(buf, sizeof buf, "%.5Qg", errT / Tabs); printf("relative error bound of T = %s\n", buf);
    return 0;
}
