"""From certified k-point minima to the line Psi_k >= s k - t and the final proportions (exact rational arithmetic).

Input per cell length H: certified lower bounds P_k >= p_k for k in a set (pair-sum minima), the anchor index K = H + 1 with the 1-D minorant
phi (40 lines certified below K_0^2 on [0, 1.06] by oned_check.py): Psi_K >= min(1, 2 (K - 1) phi(1)) (K - 1 adjacent gaps averaging at most 1,
Jensen for the convex nonincreasing phi).  tau_k = min(1, 2 p_k); tau* is the superadditive closure (Psi_{a+b} >= Psi_a + Psi_b, Psi_0 = Psi_1 = 0).
A line (s, t) with s k - t <= tau*_k for k < K and s K <= tau*_K gives Psi_k >= s k - t for all k (induction with superadditivity), hence
  n/N >= (C_0 - t/H)/(1 - s),    D/N >= (1 + C_0)/2 + (s u - t/H)/2,  u = (C_0 - t/H)/(1 - s).
C_0 = 3/2 - cot(1/sqrt(2))/sqrt(2); the rational lower bound 6725007/10^7 is used here (final_constants.py evaluates the final expressions in ball arithmetic).
"""
import sys, json
from fractions import Fraction as F

C0_LOW = F(6725007, 10 ** 7)


def phi_at(lines, g):
    return max([F(0)] + [F(str(a)) + F(str(m)) * g for a, m in lines])


def closure(tau, kmax):
    t = list(tau)
    for k in range(2, kmax + 1):
        best = t[k]
        for a in range(1, k):
            best = max(best, t[a] + t[k - a])
        t[k] = best
    return t


def best_line(H, p, K, anchor_tau, grid=20000):
    """p: dict k -> certified lower bound of P_k (k = 3 ..); returns the best (s, t) over a grid of s, with t from the base cases."""
    tau = [F(0)] * (K + 1)
    for k, v in p.items():
        tau[k] = min(F(1), 2 * v)
    tau[K] = max(tau[K], min(F(1), anchor_tau))
    tau = closure(tau, K)
    best = None
    smax = tau[K] / K
    for i in range(0, grid + 1):
        s = smax * i / grid
        t = max(F(0), max(s * k - tau[k] for k in range(0, K)))
        u = (C0_LOW - t / H) / (1 - s)
        if best is None or u > best[0]:
            best = (u, s, t)
    return best, tau


if __name__ == "__main__":
    targets = json.load(open(sys.argv[1], encoding="utf-8"))
    lines = targets["phi_lines"]
    for plan in targets["plans"]:
        H = F(str(plan["H"]))
        K = int(plan["anchor_K"])
        p = {int(k): F(str(v)) for k, v in plan["targets_P_k"].items()}
        phi1 = phi_at(lines, F(1))
        anchor = 2 * (K - 1) * phi1
        (u, s, t), tau = best_line(H, p, K, anchor)
        print("H =", H, "K =", K, "phi(1) =", float(phi1), "anchor tau_K =", float(min(F(1), anchor)))
        print("  tau* =", [float(x) for x in tau])
        print("  best line: s =", float(s), "t =", float(t), " bound u =", float(u), " gain over C0_low =", float(u - C0_LOW))
        print("  distinct >= ", float((1 + C0_LOW) / 2 + (s * u - t / H) / 2))
