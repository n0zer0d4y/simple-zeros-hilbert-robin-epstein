"""The Montgomery-Taylor kernel K_0 of Lamzouri and Wang (arXiv:2609.24167, Section 3) in python-flint ball arithmetic.

f_0(u) = cos(sqrt(2) u) / (sqrt(2) sin(1/sqrt(2))) on [-1/2, 1/2] (zero outside) is a probability density, K_0 = hat f_0,
    K_0(x) = c (sinc(A) + sinc(B)),  c = 1/(2 sqrt(2) sin(1/sqrt(2))),  A = (sqrt(2) - 2 pi x)/2,  B = (sqrt(2) + 2 pi x)/2,
    K_0'(x) = c pi (sinc'(B) - sinc'(A)),     sinc'(t) = (t cos t - sin t)/t^2.
Proven bounds (f_0 >= 0, integral 1, support in [-1/2, 1/2]):  abs(K_0) <= 1,  abs(K_0') <= pi,  abs(K_0'') <= pi^2.
"""
from flint import arb, ctx, fmpq

ctx.prec = 128
SQ2 = arb(2).sqrt()
PI = arb.pi()
C0 = 1 / (2 * SQ2 * (1 / SQ2).sin())

_FACT = [arb(1)]
for _n in range(1, 40):
    _FACT.append(_FACT[-1] * _n)


def sinc_d(t):
    """(sinc(t), sinc'(t)) as balls; series with a rigorous remainder for abs(t) < 1/100, closed form otherwise."""
    if t.abs_upper() < arb("0.01"):
        N = 6
        t2 = t * t
        s = arb(0)
        p = arb(1)                      # t^(2k)
        for k in range(0, N + 1):
            s += (-1) ** k * p / _FACT[2 * k + 1]
            p = p * t2
        # derivative series: sum_{k>=1} (-1)^k 2k t^(2k-1)/(2k+1)!
        d = arb(0)
        q = t                            # t^(2k-1) for k = 1
        for k in range(1, N + 1):
            d += (-1) ** k * 2 * k * q / _FACT[2 * k + 1]
            q = q * t2
        a = t.abs_upper()
        rem_s = a ** (2 * N + 2) / _FACT[2 * N + 3]
        rem_d = 2 * (N + 1) * a ** (2 * N + 1) / _FACT[2 * N + 3] * 2
        return s + rem_s * arb(0, 1), d + rem_d * arb(0, 1)
    sn, cs = t.sin_cos()
    return sn / t, (t * cs - sn) / (t * t)


def K0K1(x):
    """(K_0(x), K_0'(x)) for a ball x."""
    A = (SQ2 - 2 * PI * x) / 2
    B = (SQ2 + 2 * PI * x) / 2
    sA, dA = sinc_d(A)
    sB, dB = sinc_d(B)
    return C0 * (sA + sB), C0 * PI * (dB - dA)


if __name__ == "__main__":
    import mpmath as mp
    mp.mp.dps = 40
    c = 1 / (2 * mp.sqrt(2) * mp.sin(1 / mp.sqrt(2)))
    def K(x):
        A = (mp.sqrt(2) - 2 * mp.pi * x) / 2
        B = (mp.sqrt(2) + 2 * mp.pi * x) / 2
        return c * (mp.sinc(A) + mp.sinc(B)) if False else c * (mp.sin(A) / A + mp.sin(B) / B)
    print("K0(0) =", K0K1(arb(0))[0].str(30), " K0'(0) =", K0K1(arb(0))[1].str(10))
    for x in ["0.2251", "0.5", "1.0345", "2.07", "3.11", "5"]:
        xa = arb(x)
        k, kp = K0K1(xa)
        xm = mp.mpf(x)
        kk = K(xm)
        kd = mp.diff(K, xm)
        print(x, "K0 =", k.str(20), "(mp", mp.nstr(kk, 20), ")", " K0' =", kp.str(15), "(mp", mp.nstr(kd, 15), ")")
    # a point at which A is tiny: x = sqrt(2)/(2 pi) rounded
    xz = arb(fmpq(2251, 10000))
    print("near the removable point:", K0K1(xz)[0].str(20), K0K1(xz)[1].str(15))
