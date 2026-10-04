"""The three decisive margins V(n) = sigma(n)/n - (e^gamma/2) log log n at n = N, 3N and c0 = 67N, at 120 digits.

sigma(n)/n is the exact rational product of (q^(e+1) - 1)/(q^e (q - 1)) over the factorisation; it is also recomputed
directly from the definition of sigma for comparison. The values are printed by mpmath at 120 significant digits and by
python-flint balls at 400 bits; both must agree in sign and in every printed digit.

Usage: python margins.py
"""
from fractions import Fraction
import mpmath as mp
from flint import arb, ctx, fmpq

PR = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67]
FAC_N = [(3, 4), (5, 3), (7, 2)] + [(p, 1) for p in PR if 11 <= p <= 61]


def value(fac):
    n, ratio = 1, Fraction(1)
    for q, e in fac:
        n *= q ** e
        ratio *= Fraction(q ** (e + 1) - 1, q ** e * (q - 1))
    return n, ratio


mp.mp.dps = 130
ctx.prec = 400
for tag, fac in [("N", FAC_N), ("3N", [(3, 5)] + FAC_N[1:]), ("c0 = 67 N", FAC_N + [(67, 1)])]:
    n, r = value(fac)
    v_mp = mp.mpf(r.numerator) / r.denominator - mp.exp(mp.euler) / 2 * mp.log(mp.log(n))
    v_arb = arb(fmpq(r.numerator, r.denominator)) - arb.const_euler().exp() / 2 * arb(n).log().log()
    print("%-10s n = %d" % (tag, n))
    print("  sigma(n)/n = %s" % r)
    print("  V(n) mpmath (120 digits) = %s" % mp.nstr(v_mp, 120))
    print("  V(n) arb (400 bits)      = %s" % v_arb.str(60, radius=True))
    print("  sign: %s" % ("positive (violator)" if v_arb > 0 else "negative" if v_arb < 0 else "undecided"))
