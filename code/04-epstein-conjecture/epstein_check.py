"""Betermin-Samaj-Travenec Conjecture 1.1 (arXiv:2110.09368): the unique zero of
zeta2(1/2, Delta) = (1/2) sum'_{j,k} (j^2 + Delta^2 k^2)^(-1/2) (analytic continuation), Delta in (0,1),
is Delta* = e^gamma / (4 pi)?  They report agreement 'by at least 22 decimal digits'.

Two independent evaluations of Z(1/2,Delta) = sqrt(Delta) * zeta2(1/2, Delta)   [Z(s,D) = (D/pi)^s Gamma(s) zeta2(s,D)]:
 (I)  Riemann's method from the definition:
        Z(s,D) = 1/2 int_0^inf t^(s-1) [theta3(e^{-pi t/D}) theta3(e^{-pi t D}) - 1] dt
               = -1/(2s) - 1/(2(1-s)) + 1/2 int_1^inf (t^(s-1) + t^(-s)) [theta3(e^{-pi t D}) theta3(e^{-pi t/D}) - 1] dt
      so Z(1/2,D) = -2 + int_1^inf t^(-1/2) [theta(t) - 1] dt.
 (II) Bessel series (Chowla-Selberg type):  Z(1/2,D) = [ gamma - log(4 pi D) + 4 sum_{N>=1} d(N) K_0(2 pi N / D) ] / sqrt(D).
At D* = e^gamma/(4 pi) the first two terms of (II) cancel exactly and the remaining terms are positive, so Z(1/2,D*) > 0.
This script checks (I) = (II) to ~50 digits and locates the true root. mpmath, 70 digits (numeric-experiment;
the decisive inequality is re-derived rigorously in main.md and re-evaluated with Arb in epstein_arb.py).
"""
import mpmath as mp
from sympy import divisor_count

mp.mp.dps = 70

def Z_int(D):
    D = mp.mpf(D)
    f = lambda t: t ** (-mp.mpf(1) / 2) * (mp.jtheta(3, 0, mp.exp(-mp.pi * t * D)) * mp.jtheta(3, 0, mp.exp(-mp.pi * t / D)) - 1)
    pts = [1, 3, 10, 30, 100, 300, 1000]
    return -2 + mp.quad(f, pts)

def Z_bes(D, nmax=12):
    D = mp.mpf(D)
    s = sum(int(divisor_count(N)) * mp.besselk(0, 2 * mp.pi * N / D) for N in range(1, nmax + 1))
    return (mp.euler - mp.log(4 * mp.pi * D) + 4 * s) / mp.sqrt(D)

Dstar = mp.exp(mp.euler) / (4 * mp.pi)
print("Delta* = e^gamma/(4 pi) =", mp.nstr(Dstar, 40))
zi = Z_int(Dstar)
zb = Z_bes(Dstar)
print("Z(1/2, Delta*) via (I) theta integral :", mp.nstr(zi, 30))
print("Z(1/2, Delta*) via (II) Bessel series :", mp.nstr(zb, 30))
print("difference (I)-(II):", mp.nstr(zi - zb, 5))
# check agreement at a couple of other Delta
for D in ("0.3", "0.14", "0.9"):
    a, b = Z_int(D), Z_bes(D)
    print("Delta=%s  (I)=%s  (II)=%s  diff=%s" % (D, mp.nstr(a, 25), mp.nstr(b, 25), mp.nstr(a - b, 3)))
# true root
root = mp.findroot(lambda D: Z_bes(D), Dstar * (1 + mp.mpf("1e-19")), tol=mp.mpf(10) ** -60)
print("true root Delta_c  =", mp.nstr(root, 45))
print("e^gamma/(4 pi)     =", mp.nstr(Dstar, 45))
print("Delta_c - e^gamma/(4 pi) =", mp.nstr(root - Dstar, 12), "  relative", mp.nstr((root - Dstar) / Dstar, 8))
print("check Z_int(root) =", mp.nstr(Z_int(root), 8))
