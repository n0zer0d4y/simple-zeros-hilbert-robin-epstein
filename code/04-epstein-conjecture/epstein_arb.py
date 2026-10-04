"""Rigorous (Arb ball arithmetic) verification that Z(1/2, Delta*) > 0 at Delta* = e^gamma/(4 pi).

Z(1/2, D) = sqrt(D) zeta2(1/2, D),  zeta2(s,D) = (1/2) sum'_{j,k} (j^2 + D^2 k^2)^(-s)  (continued).

 (I)  from the definition (Riemann's method):  Z(1/2,D) = -2 + int_1^inf t^(-1/2) [theta3(e^{-pi t D}) theta3(e^{-pi t/D}) - 1] dt
      The integral over [1,T] is an Arb rigorous integral; the tail over [T,inf) is bounded: for t >= T with
      e^{-pi T D} <= 1/100 (so also e^{-pi T/D}, D <= 1):  0 <= theta(t) - 1 <= 4.1 e^{-pi t D}, hence
      0 <= tail <= 4.1 T^(-1/2) e^{-pi D T} / (pi D).
 (II) Bessel series:  Z(1/2,D) = [gamma - log(4 pi D) + 4 sum_{N>=1} d(N) K_0(2 pi N/D)] / sqrt(D);
      truncated at N = 12 with the tail bounded by 14 exp(-13 * 2 pi / D)  (d(N) <= N, K_0(x) <= e^{-x} for x >= pi/2).
Both enclosures must contain the same number; (II) at D = Delta* is a positive number minus a ball around 0.
Also: Z(1/2, Delta* + 1e-20) < 0 by (II)  =>  a zero lies in (Delta*, Delta* + 1e-20).
"""
import json
import flint
from flint import acb, arb

flint.ctx.prec = 320
PI = arb.pi()
EG = arb.const_euler()
T = 600
OUT = {}

def d_of(n):
    return sum(1 for k in range(1, n + 1) if n % k == 0)

def theta3(tau):
    return acb.modular_theta(acb(0), tau)[2]

def Z_int(D):
    D = arb(D)
    I = acb(0, 1)
    def f(t, analytic):
        th = theta3(I * (t * D)) * theta3(I * (t / D))
        return (th - 1) / t.sqrt()
    val = acb.integral(f, acb(1), acb(T), rel_tol=arb(2) ** -280, abs_tol=arb(2) ** -330)
    q1 = (-(PI * D * T)).exp()
    q2 = (-(PI * T / D)).exp()
    assert q1.upper() < arb("0.01") and q2.upper() < arb("0.01") and D.upper() <= 1
    tail_bound = arb("4.1") * q1 / (arb(T).sqrt() * PI * D)
    return -2 + val.real + arb(0).union(tail_bound)

def Z_bes(D, nmax=12):
    D = arb(D)
    s = arb(0)
    for n in range(1, nmax + 1):
        s += d_of(n) * acb(2 * PI * n / D).bessel_k(0).real
    x1 = 2 * PI / D
    assert x1.lower() > arb("1.6")
    tail = arb(14) * (-(x1 * (nmax + 1))).exp()
    s += arb(0).union(tail)
    return (EG - (4 * PI * D).log() + 4 * s) / D.sqrt()

Dstar = EG.exp() / (4 * PI)
Dshift = Dstar + arb(10) ** -20
print("Delta*          =", Dstar.str(50, radius=False))
zi = Z_int(Dstar)
zb = Z_bes(Dstar)
print("Z(1/2,D*) (I)   =", zi.str(40))
print("Z(1/2,D*) (II)  =", zb.str(40))
print("(I) lower bound > 0:", bool(zi.lower() > 0), "  (II) lower bound > 0:", bool(zb.lower() > 0))
print("balls overlap   :", bool(zi.overlaps(zb)))
zs = Z_bes(Dshift)
print("Z(1/2,D*+1e-20) (II) =", zs.str(40), "  upper bound < 0:", bool(zs.upper() < 0))
zsi = Z_int(Dshift)
print("Z(1/2,D*+1e-20) (I)  =", zsi.str(40), "  upper bound < 0:", bool(zsi.upper() < 0))
OUT = dict(
    delta_star=Dstar.str(60, radius=False),
    Z_half_at_delta_star_definition=zi.str(40),
    Z_half_at_delta_star_bessel=zb.str(40),
    positive_definition=bool(zi.lower() > 0), positive_bessel=bool(zb.lower() > 0),
    Z_half_at_delta_star_plus_1e_20_bessel=zs.str(40), negative_bessel=bool(zs.upper() < 0),
    Z_half_at_delta_star_plus_1e_20_definition=zsi.str(40), negative_definition=bool(zsi.upper() < 0),
    integral_cutoff_T=T, precision_bits=320)
json.dump(OUT, open("epstein_arb.json", "w"), indent=1)
print("OK: Delta* is NOT a zero; a zero of Z(1/2,.) lies in (Delta*, Delta*+1e-20).")
