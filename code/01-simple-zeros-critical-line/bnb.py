"""Certified lower bounds for the k-point energies of the Montgomery-Taylor kernel (Wang arXiv:2609.24167, Lemma 3.2 and its extension).

  m(H)  = min over {u, v >= 0, u + v <= H} of  g(u, v)  = K_0(u)^2 + K_0(v)^2 + K_0(u+v)^2           (three points in an interval of length H)
  P4(H) = min over {a, b, c >= 0, a + b + c <= H} of f(a, b, c) = K_0(a)^2 + K_0(b)^2 + K_0(c)^2 + K_0(a+b)^2 + K_0(b+c)^2 + K_0(a+b+c)^2

Feasibility branch and bound with python-flint balls: a target tau is certified (min >= tau) when every cell of a covering of the
domain has a rigorous lower bound >= tau.  Taylor bound on a cell of half-width r about its centre c (all derivatives of K_0 bounded
by the proven abs(K_0) <= 1, abs(K_0') <= pi, abs(K_0'') <= pi^2, hence abs((K_0^2)'') <= 4 pi^2):
  2-D:  g >= g(c) - (abs(g_u(c)) + abs(g_v(c))) r - 125 r^2          (Hessian Frobenius norm <= pi^2 sqrt(160) < 125, abs(h)^2 <= 2 r^2)
  3-D:  f >= f(c) - (abs(f_a) + abs(f_b) + abs(f_c)) r - 592.5 r^2   (Hessian operator norm <= 40 pi^2 < 395, abs(h)^2 <= 3 r^2)
By the symmetry of the domain (u <-> v, resp. a <-> c) only cells meeting {u <= v} (resp. {a <= c}) are kept.
Lattice bookkeeping: level L has half-width r_L = H/(2 n0 2^L); a cell (i, j[, k]) has centre ((2i+1) r_L, (2j+1) r_L[, (2k+1) r_L]);
every argument of K_0 is an integer multiple of r_L, so K_0, K_0' are cached per (level, integer).
"""
import sys, time, json
from fractions import Fraction
from flint import arb, ctx, fmpq
import kernel
from kernel import K0K1, PI

ctx.prec = 128


class Lattice:
    def __init__(self, H, n0):
        self.H = Fraction(H)
        self.n0 = n0
        self.cache = {}
        self.rs = {}

    def r(self, L):
        if L not in self.rs:
            fr = self.H / (2 * self.n0 * 2 ** L)
            self.rs[L] = arb(fmpq(fr.numerator, fr.denominator))
        return self.rs[L]

    def K(self, L, idx):
        key = (L, idx)
        v = self.cache.get(key)
        if v is None:
            v = K0K1(self.r(L) * idx)
            self.cache[key] = v
        return v


def abs_arb(x):
    return abs(x)


def bnb2(H, tau, n0=200, max_level=14, verbose=True):
    """certify min over T_H of g >= tau.  Returns dict with counts; raises if a cell cannot be closed at max_level."""
    lat = Lattice(H, n0)
    tau_a = arb(tau) if not isinstance(tau, Fraction) else arb(fmpq(tau.numerator, tau.denominator))
    cells = [(i, j) for i in range(n0) for j in range(n0) if j >= i - 1 and i + j <= n0]
    L = 0
    n_dropped = 0
    n_eval = 0
    min_lb = None
    t0 = time.time()
    per_level = []
    while cells:
        if L > max_level:
            raise RuntimeError("cells remain at level %d: %d" % (L, len(cells)))
        r = lat.r(L)
        r2 = 125 * r * r
        nxt = []
        Nn = n0 * 2 ** L
        for (i, j) in cells:
            Ku, Kpu = lat.K(L, 2 * i + 1)
            Kv, Kpv = lat.K(L, 2 * j + 1)
            Kw, Kpw = lat.K(L, 2 * i + 2 * j + 2)
            g = Ku * Ku + Kv * Kv + Kw * Kw
            cw = Kw * Kpw
            gu = 2 * (Ku * Kpu + cw)
            gv = 2 * (Kv * Kpv + cw)
            lb = g - (abs(gu) + abs(gv)) * r - r2
            lo = lb.lower()
            n_eval += 1
            if lo >= tau_a:
                n_dropped += 1
                if min_lb is None or lo < min_lb:
                    min_lb = lo
            else:
                nxt.append((i, j))
        per_level.append((L, len(cells), len(nxt)))
        if verbose:
            print("level", L, "cells", len(cells), "survivors", len(nxt), "t=%.1fs" % (time.time() - t0), flush=True)
        # split survivors, keep only children meeting {u <= v} and u + v <= H (+ margin)
        L += 1
        Nn2 = n0 * 2 ** L
        cells = []
        for (i, j) in nxt:
            for di in (0, 1):
                for dj in (0, 1):
                    ci, cj = 2 * i + di, 2 * j + dj
                    if cj >= ci - 1 and ci + cj <= Nn2:
                        cells.append((ci, cj))
    return {"H": str(H), "tau": str(tau), "n0": n0, "cells_evaluated": n_eval, "cells_dropped": n_dropped,
            "levels": per_level, "min_dropped_lb": min_lb.str(12) if min_lb is not None else None,
            "seconds": time.time() - t0, "certified": True}


def bnb3(H, tau, n0=48, max_level=12, verbose=True):
    """certify min over {a,b,c >= 0, a+b+c <= H} of f >= tau."""
    lat = Lattice(H, n0)
    tau_a = arb(tau) if not isinstance(tau, Fraction) else arb(fmpq(tau.numerator, tau.denominator))
    # cell (i, j, k): a = (2i+1) r, b = (2j+1) r, c = (2k+1) r; keep iff c_c >= c_a - 2r  (k >= i - 1),
    # c_a + c_b + c_c <= H + 3r  <=>  (2i + 2j + 2k + 3) <= 2 Nn + 3  <=>  i + j + k <= Nn
    cells = [(i, j, k) for i in range(n0) for j in range(n0) for k in range(n0) if k >= i - 1 and i + j + k <= n0]
    L = 0
    n_dropped = 0
    n_eval = 0
    min_lb = None
    t0 = time.time()
    per_level = []
    while cells:
        if L > max_level:
            raise RuntimeError("cells remain at level %d: %d" % (L, len(cells)))
        r = lat.r(L)
        r2 = arb(fmpq(1185, 2)) * r * r
        nxt = []
        for (i, j, k) in cells:
            Ka, Kpa = lat.K(L, 2 * i + 1)
            Kb, Kpb = lat.K(L, 2 * j + 1)
            Kc, Kpc = lat.K(L, 2 * k + 1)
            Kab, Kpab = lat.K(L, 2 * (i + j + 1))
            Kbc, Kpbc = lat.K(L, 2 * (j + k + 1))
            Kabc, Kpabc = lat.K(L, 2 * (i + j + k) + 3)
            f = Ka * Ka + Kb * Kb + Kc * Kc + Kab * Kab + Kbc * Kbc + Kabc * Kabc
            pa, pb, pc = Ka * Kpa, Kb * Kpb, Kc * Kpc
            pab, pbc, pabc = Kab * Kpab, Kbc * Kpbc, Kabc * Kpabc
            fa = 2 * (pa + pab + pabc)
            fb = 2 * (pb + pab + pbc + pabc)
            fc = 2 * (pc + pbc + pabc)
            lb = f - (abs(fa) + abs(fb) + abs(fc)) * r - r2
            lo = lb.lower()
            n_eval += 1
            if lo >= tau_a:
                n_dropped += 1
                if min_lb is None or lo < min_lb:
                    min_lb = lo
            else:
                nxt.append((i, j, k))
        per_level.append((L, len(cells), len(nxt)))
        if verbose:
            print("level", L, "cells", len(cells), "survivors", len(nxt), "t=%.1fs" % (time.time() - t0), flush=True)
        L += 1
        Nn2 = n0 * 2 ** L
        cells = []
        for (i, j, k) in nxt:
            for di in (0, 1):
                for dj in (0, 1):
                    for dk in (0, 1):
                        ci, cj, ck = 2 * i + di, 2 * j + dj, 2 * k + dk
                        if ck >= ci - 1 and ci + cj + ck <= Nn2:
                            cells.append((ci, cj, ck))
    return {"H": str(H), "tau": str(tau), "n0": n0, "cells_evaluated": n_eval, "cells_dropped": n_dropped,
            "levels": per_level, "min_dropped_lb": min_lb.str(12) if min_lb is not None else None,
            "seconds": time.time() - t0, "certified": True}


if __name__ == "__main__":
    mode = sys.argv[1]
    H = Fraction(sys.argv[2])
    tau = Fraction(sys.argv[3])
    n0 = int(sys.argv[4]) if len(sys.argv) > 4 else None
    if mode == "m3":
        res = bnb2(H, tau, n0 or 200)
    elif mode == "p4":
        res = bnb3(H, tau, n0 or 48)
    else:
        raise SystemExit("mode m3 or p4")
    print(json.dumps(res))
    json.dump(res, open("bnb_%s_H%s_tau%s.json" % (mode, str(H).replace("/", "_"), float(tau)), "w"), indent=1)
