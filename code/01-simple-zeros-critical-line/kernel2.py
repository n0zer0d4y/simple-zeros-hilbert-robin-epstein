"""Enclosures of K_0, K_0', K_0'' over a ball (for local Hessian bounds), python-flint balls.

K_0'' = c pi^2 (sinc''(A) + sinc''(B)),  sinc''(t) = ((2 - t^2) sin t - 2 t cos t)/t^3.
Universal bounds (sinc(t) = int_0^1 cos(ts) ds): abs(sinc^(n)) <= 1/(n+1), sinc >= -0.2173; they are used when a ball is wide
and touches the removable point t = 0.
"""
from flint import arb, ctx
from kernel import SQ2, PI, C0

ctx.prec = 128
_FACT = [arb(1)]
for _n in range(1, 64):
    _FACT.append(_FACT[-1] * _n)

ctx.prec = 128
_HALF = arb("0.5")
_THIRD = arb(1) / 3
_PI2 = PI * PI
_SMALL = arb("0.01")


def sinc012(t):
    """(sinc t, sinc' t, sinc'' t) as enclosures valid for every real point of the ball t.

    Taylor series with a rigorous remainder for abs(t) <= 4 (the closed forms lose all digits for wide balls near 0), closed forms
    for balls with abs(t) >= 4 everywhere, universal bounds otherwise."""
    a_up = t.abs_upper()
    if a_up <= 4:
        N = 24
        t2 = t * t
        s = arb(0)
        p = arb(1)
        for k in range(0, N + 1):
            s += (-1) ** k * p / _FACT[2 * k + 1]
            p = p * t2
        d = arb(0)
        q = t
        for k in range(1, N + 1):
            d += (-1) ** k * 2 * k * q / _FACT[2 * k + 1]
            q = q * t2
        e = arb(0)
        q2 = arb(1)
        for k in range(1, N + 1):
            e += (-1) ** k * (2 * k) * (2 * k - 1) * q2 / _FACT[2 * k + 1]
            q2 = q2 * t2
        a = a_up
        # alternating-type tails, bounded by a few times the first omitted terms (a <= 4, 2N + 3 = 51 so the terms are below 1e-36)
        rem_s = a ** (2 * N + 2) / _FACT[2 * N + 3] * 2
        rem_d = 2 * (N + 1) * a ** (2 * N + 1) / _FACT[2 * N + 3] * 4
        rem_e = (2 * N + 2) * (2 * N + 1) * a ** (2 * N) / _FACT[2 * N + 3] * 4
        return s + rem_s * arb(0, 1), d + rem_d * arb(0, 1), e + rem_e * arb(0, 1)
    if t.abs_lower() >= 4:
        sn, cs = t.sin_cos()
        t2 = t * t
        return sn / t, (t * cs - sn) / t2, ((2 - t2) * sn - 2 * t * cs) / (t2 * t)
    return arb(0, 1), arb(0, 1) * _HALF, arb(0, 1) * _THIRD


def K012(x):
    """(K_0, K_0', K_0'') over the ball x."""
    A = (SQ2 - 2 * PI * x) / 2
    B = (SQ2 + 2 * PI * x) / 2
    sA, dA, eA = sinc012(A)
    sB, dB, eB = sinc012(B)
    return C0 * (sA + sB), C0 * PI * (dB - dA), C0 * _PI2 * (eA + eB)


if __name__ == "__main__":
    import mpmath as mp
    mp.mp.dps = 30
    c = 1 / (2 * mp.sqrt(2) * mp.sin(1 / mp.sqrt(2)))
    def K(x):
        return c * (mp.sin((mp.sqrt(2) - 2 * mp.pi * x) / 2) / ((mp.sqrt(2) - 2 * mp.pi * x) / 2) + mp.sin((mp.sqrt(2) + 2 * mp.pi * x) / 2) / ((mp.sqrt(2) + 2 * mp.pi * x) / 2))
    for x in ["0.3", "1.0345", "2.07", "0.2251"]:
        k, kp, kpp = K012(arb(x))
        print(x, "K0'' =", kpp.str(15), "(mp", mp.nstr(mp.diff(K, mp.mpf(x), 2), 15), ")")
    kb = K012(arb(1.0345).union(arb(1.0349)))
    print("ball [1.0345, 1.0349]:", [v.str(8) for v in kb])
    kb = K012(arb(0.2).union(arb(0.25)))
    print("ball touching the removable point:", [v.str(8) for v in kb])
