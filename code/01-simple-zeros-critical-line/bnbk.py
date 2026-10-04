"""Certified lower bound of the k-point pair energy of K_0 in an interval of length H, any k (python-flint balls, local Hessian enclosures).

  P_k(H) = min over gaps g_1..g_{k-1} >= 0 with sum <= H of  E(g) = sum over pairs (a < b) of K_0(g_{a+1} + ... + g_b)^2,

Feasibility branch and bound (min >= tau).  On a cube cell of half-width r about the centre c (d = k - 1 gaps):
  E(c + h) >= E(c) - r sum_l abs(G_l) - (r^2/2) sum_e w_e^2 max(0, -m_e)
with G_l = sum over windows e containing gap l of 2 K(t_e) K'(t_e), t_e = e . c, w_e = number of gaps in the window, and
m_e a rigorous lower bound of (K_0^2)'' = 2 K'^2 + 2 K K'' over the interval X_e = [t_e - w_e r, t_e + w_e r] (ball enclosures of K, K', K'';
(K_0^2)'' >= 2 (inf abs K')^2 + 2 inf(K K'')).  Proof: Taylor with integral remainder, e . (c + s h) in X_e for s in [0, 1],
(e . h)^2 in [0, (w_e r)^2], so each window contributes at least -(1/2) max(0, -m_e) (w_e r)^2.
Lattice bookkeeping as in bnb.py: level L half-width r_L = H/(2 n0 2^L), cell (i_1..i_d) has centre ((2 i_l + 1) r_L); the window argument is
an integer multiple of r_L; centre values and window enclosures are cached per (level, index[, width]).
Cells meeting the symmetric half (reversal g_l <-> g_{d+1-l}) are kept: i_d >= i_1 - 1, and sum i_l <= n0 2^L.
"""
import sys, time, json
from fractions import Fraction
from flint import arb, ctx, fmpq
from kernel import K0K1
from kernel2 import K012

ctx.prec = 128


class Ctx:
    def __init__(self, H, n0, d):
        self.H = Fraction(H)
        self.n0 = n0
        self.d = d
        self.rs = {}
        self.cen = {}      # (L, idx) -> (K^2, 2 K K')
        self.neg = {}      # (L, idx, w) -> w^2 * upper bound of max(0, -m_e)
        self.pairs = [(a, b) for a in range(d + 1) for b in range(a + 1, d + 1)]

    def r(self, L):
        v = self.rs.get(L)
        if v is None:
            fr = self.H / (2 * self.n0 * 2 ** L)
            v = arb(fmpq(fr.numerator, fr.denominator))
            self.rs[L] = v
        return v

    def centre(self, L, idx):
        v = self.cen.get((L, idx))
        if v is None:
            k, kp = K0K1(self.r(L) * idx)
            v = (k * k, 2 * k * kp)
            self.cen[(L, idx)] = v
        return v

    def negpart(self, L, idx, w):
        key = (L, idx, w)
        v = self.neg.get(key)
        if v is None:
            r = self.r(L)
            X = (r * idx) + (r * w) * arb(0, 1)
            k, kp, kpp = K012(X)
            # inf of 2 K'^2 + 2 K K'' over the ball: 2 (inf abs K')^2 + 2 min of the four endpoint products of K and K''
            klo, khi = k.lower(), k.upper()
            qlo, qhi = kpp.lower(), kpp.upper()
            prods = [klo * qlo, klo * qhi, khi * qlo, khi * qhi]
            pmin = prods[0]
            for p in prods[1:]:
                if float(p.mid()) < float(pmin.mid()):
                    pmin = p
            al = kp.abs_lower()
            m = 2 * al * al + 2 * pmin
            t = (-m).upper()
            if float(t.mid()) <= 0:
                t = arb(0)
            v = t * (w * w)
            self.neg[key] = v
        return v


def certify(H, k, tau, n0=8, max_level=24, verbose=True, max_cells=None, log_every=0):
    """certify min over the gap simplex of the k-point energy >= tau.  Raises on failure; returns a summary dict."""
    d = k - 1
    cx = Ctx(H, n0, d)
    tau_a = arb(fmpq(Fraction(tau).numerator, Fraction(tau).denominator))
    pairs = cx.pairs
    # initial cells
    def children_filter(cell, Nn):
        return cell[d - 1] >= cell[0] - 1 and sum(cell) <= Nn
    cells0 = []
    def rec(prefix, left):
        if len(prefix) == d:
            c = tuple(prefix)
            if c[d - 1] >= c[0] - 1:
                cells0.append(c)
            return
        for i in range(0, left + 1):
            rec(prefix + [i], left - i)
    rec([], n0)
    stack = [(0, c) for c in cells0]
    n_eval = n_drop = 0
    max_L = 0
    t0 = time.time()
    per_level = {}
    half = arb(1) / 2
    min_lb = None
    while stack:
        L, cell = stack.pop()
        n_eval += 1
        if L > max_L:
            max_L = L
        per_level[L] = per_level.get(L, 0) + 1
        if log_every and n_eval % log_every == 0:
            print('progress: cells %d, stack %d, max level %d, dropped %d, t=%.0fs' % (n_eval, len(stack), max_L, n_drop, time.time() - t0), flush=True)
        if max_cells is not None and n_eval > max_cells:
            raise RuntimeError("cell budget exceeded (%d); max level %d" % (max_cells, max_L))
        r = cx.r(L)
        # prefix sums of (2 i + 1)
        P = [0]
        for i in cell:
            P.append(P[-1] + 2 * i + 1)
        E = arb(0)
        G = [arb(0)] * d
        G = [arb(0) for _ in range(d)]
        rem = arb(0)
        for (a, b) in pairs:
            idx = P[b] - P[a]
            k2, v = cx.centre(L, idx)
            E += k2
            for l in range(a, b):
                G[l] += v
            rem += cx.negpart(L, idx, b - a)
        gsum = arb(0)
        for g in G:
            gsum += abs(g)
        lb = E - r * gsum - half * r * r * rem
        lo = lb.lower()
        if lo >= tau_a:
            n_drop += 1
            if min_lb is None or float(lo.mid()) < float(min_lb.mid()):
                min_lb = lo
            continue
        if L >= max_level:
            raise RuntimeError("cell not closed at max level %d: %s" % (L, cell))
        Nn2 = n0 * 2 ** (L + 1)
        # split into 2^d children
        stack_children = [()]
        for i in cell:
            stack_children = [pre + (2 * i + e,) for pre in stack_children for e in (0, 1)]
        for ch in stack_children:
            if ch[d - 1] >= ch[0] - 1 and sum(ch) <= Nn2:
                stack.append((L + 1, ch))
    return {"H": str(H), "k": k, "tau": str(tau), "n0": n0, "cells_evaluated": n_eval, "cells_dropped": n_drop,
            "max_level": max_L, "per_level": per_level, "min_dropped_lb": min_lb.str(10) if min_lb is not None else None,
            "seconds": time.time() - t0, "certified": True}


if __name__ == "__main__":
    H = Fraction(sys.argv[1])
    k = int(sys.argv[2])
    tau = Fraction(sys.argv[3])
    n0 = int(sys.argv[4]) if len(sys.argv) > 4 else 8
    max_cells = int(sys.argv[5]) if len(sys.argv) > 5 else None
    res = certify(H, k, tau, n0=n0, max_cells=max_cells)
    print(json.dumps(res))
    json.dump(res, open("bnbk_H%s_k%d_tau%s.json" % (str(H).replace("/", "_"), k, float(tau)), "w"), indent=1)
