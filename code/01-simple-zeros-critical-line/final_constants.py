"""Final constants of result 1 in ball arithmetic (python-flint, 256 bits), and an exact-rational check of every
inequality that the lines (s, t) need.

C_0 = 3/2 - cot(1/sqrt 2)/sqrt 2 (Alpoge-Furman, Lamzouri). A line Psi_k >= s k - t for all k gives
    simple:   n/N >= u := (C_0 - t/H)/(1 - s)
    distinct: D/N >= (1 + C_0)/2 + (s u - t/H)/2.
Cell length 4 uses the line s = Psi_3, t = 2 Psi_3 with Psi_3 = 2 m(4). Cell lengths 7 and 8 use the outward-rounded lines
below. The certified inputs are the lower bounds in certificates/01-simple-zeros-critical-line/ (cells-H4.json,
cells-H7-H8.json) and phi(1) >= 141397/(5*10^7) (the best of the 40 lines at g = 1; see oned_check.py and the Lean file
SimpleZerosHilbertRobinEpstein/SimpleZeros/WangCellAnchor.lean).

Usage: python final_constants.py
"""
from fractions import Fraction as F
from flint import arb, ctx

ctx.prec = 256

SQ2 = arb(2).sqrt()
C0 = arb(3) / 2 - (1 / SQ2).cot() / SQ2
PHI1 = F(141397, 50_000_000)          # phi(1), exact best line at g = 1


def bounds(s, t, H):
    s_, t_ = arb(s.numerator) / s.denominator, arb(t.numerator) / t.denominator
    u = (C0 - t_ / H) / (1 - s_)
    d = (1 + C0) / 2 + (s_ * u - t_ / H) / 2
    return u, d


def check_line(name, s, t, K, tau):
    """tau[k]: certified lower bound for Psi_k (k = 0..K). Checks s k - t <= tau[k] for k < K and s K <= tau[K]."""
    ok = all(s * k - t <= tau[k] for k in range(K)) and s * K <= tau[K]
    print("  %s: base cases k < %d and anchor at %d hold exactly: %s" % (name, K, K, ok))
    return ok


def closure(tau):
    t = list(tau)
    for k in range(2, len(t)):
        for a in range(1, k):
            t[k] = max(t[k], t[a] + t[k - a])
    return t


print("C_0 =", C0.str(40, radius=True))

# H = 4: Psi_3 >= 2 m(4) with m(4) >= 0.000221935; Psi_4 >= 2 P_4(4) >= 2 * 0.0009 >= 4 Psi_3
m4, p4 = F(221935, 10 ** 9), F(9, 10 ** 4)
psi3 = 2 * m4
print("\nH = 4:  Psi_4 >= 4 Psi_3 (needs 2 * 0.0009 >= 4 * 2 * m(4)):", 2 * p4 >= 4 * psi3)
u, d = bounds(psi3, 2 * psi3, 4)
print("  simple   >=", u.str(30, radius=True))
print("  gain     =", (u - C0).str(10, radius=True))
print("  distinct >=", d.str(30, radius=True))

# H = 7: certified P_k(7) for k = 3..6; anchor K = 8: Psi_8 >= min(1, 14 phi(1))
P7 = {3: F("0.0000113307"), 4: F("0.000143197"), 5: F("0.000752866"), 6: F("0.0030683")}
tau = [F(0)] * 9
for k, v in P7.items():
    tau[k] = min(F(1), 2 * v)
tau[8] = min(F(1), 14 * PHI1)
tau = closure(tau)
s7, t7 = F(12194, 10 ** 7), F(45914, 10 ** 7)
print("\nH = 7:  s = %s, t = %s" % (s7, t7))
check_line("H = 7", s7, t7, 8, tau)
u, d = bounds(s7, t7, 7)
print("  simple   >=", u.str(30, radius=True))
print("  gain     =", (u - C0).str(10, radius=True))
print("  distinct >=", d.str(30, radius=True))

# H = 8: certified P_k(8) for k = 3..6 and P_7(8) >= 0.00375; anchor K = 9: Psi_9 >= min(1, 16 phi(1))
P8 = {3: F("0.00000643552"), 4: F("0.0000705725"), 5: F("0.000491377"), 6: F("0.0015534"), 7: F("0.00375")}
tau = [F(0)] * 10
for k, v in P8.items():
    tau[k] = min(F(1), 2 * v)
tau[9] = min(F(1), 16 * PHI1)
tau = closure(tau)
s8, t8 = F(21240, 10 ** 7), F(96373, 10 ** 7)
print("\nH = 8:  s = %s, t = %s" % (s8, t8))
check_line("H = 8", s8, t8, 9, tau)
u, d = bounds(s8, t8, 8)
print("  simple   >=", u.str(30, radius=True))
print("  gain     =", (u - C0).str(10, radius=True))
print("  distinct >=", d.str(30, radius=True))
