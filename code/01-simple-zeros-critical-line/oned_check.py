"""1-D check for the convex minorant phi(g) = max(0, max_i (a_i + m_i g)) of K_0^2 (python-flint balls).

For each line i certify  D_i(g) = K_0(g)^2 - a_i - m_i g >= 0  for every g in [0, 1.06], by branch and bound with the local second-derivative
enclosure (Taylor with remainder: D(c + h) >= D(c) - abs(D'(c)) r - (r^2/2) max(0, -inf (K_0^2)'' over the cell)), and check in exact rational
arithmetic that every line is non-positive for g >= 1.06 (slopes negative, a_i + 1.06 m_i <= 0), so that phi <= K_0^2 on all of [0, infinity).
Usage: python oned_check.py <targets.json>
"""
import sys, json, time
from fractions import Fraction
from flint import arb, ctx, fmpq
from kernel import K0K1
from kernel2 import K012

ctx.prec = 128


def to_arb(fr):
    return arb(fmpq(fr.numerator, fr.denominator))


def certify_line(a, m, G=Fraction(106, 100), n0=64, max_level=40):
    a_b, m_b = to_arb(a), to_arb(m)
    cells = [(Fraction(2 * i + 1) * G / (2 * n0), G / (2 * n0)) for i in range(n0)]
    stack = list(cells)
    n_eval = 0
    min_lb = None
    while stack:
        c, r = stack.pop()
        n_eval += 1
        cb, rb = to_arb(c), to_arb(r)
        k, kp = K0K1(cb)
        D = k * k - a_b - m_b * cb
        Dp = 2 * k * kp - m_b
        X = cb + rb * arb(0, 1)
        kk, kkp, kkpp = K012(X)
        klo, khi, qlo, qhi = kk.lower(), kk.upper(), kkpp.lower(), kkpp.upper()
        prods = [klo * qlo, klo * qhi, khi * qlo, khi * qhi]
        pmin = min(prods, key=lambda p: float(p.mid()))
        al = kkp.abs_lower()
        m2 = 2 * al * al + 2 * pmin
        neg = (-m2).upper()
        if float(neg.mid()) <= 0:
            neg = arb(0)
        lb = D - abs(Dp) * rb - arb(1) / 2 * rb * rb * neg
        lo = lb.lower()
        if float(lo.mid()) >= 0 and lo >= 0:
            if min_lb is None or float(lo.mid()) < float(min_lb.mid()):
                min_lb = lo
            continue
        if r < Fraction(1, 2 ** max_level):
            raise RuntimeError("line not certified: cell centre %s" % float(c))
        h = r / 2
        stack.append((c - h, h))
        stack.append((c + h, h))
    return n_eval, min_lb


if __name__ == "__main__":
    d = json.load(open(sys.argv[1], encoding="utf-8"))
    lines = d["phi_lines"]
    ok_tail = True
    total = 0
    worst = None
    t0 = time.time()
    for i, (a, m) in enumerate(lines):
        fa, fm = Fraction(str(a)), Fraction(str(m))
        assert fm < 0, "slope must be negative"
        if fa + fm * Fraction(106, 100) > 0:
            ok_tail = False
            print("line", i, "is positive at g = 1.06:", float(fa + fm * Fraction(106, 100)))
        n, mlb = certify_line(fa, fm)
        total += n
        v = float(mlb.mid()) if mlb is not None else None
        if worst is None or (v is not None and v < worst):
            worst = v
        print("line %2d: a = %s m = %s certified with %d cells, smallest lower bound %s" % (i, a, m, n, mlb.str(5) if mlb is not None else None), flush=True)
    print("ALL LINES CERTIFIED on [0, 1.06]:", total, "cells,", "tail check (each line <= 0 at 1.06):", ok_tail, "t=%.1fs" % (time.time() - t0))
    json.dump({"lines": len(lines), "cells": total, "tail_ok": ok_tail, "smallest_lower_bound": worst}, open("oned_check.out.json", "w"))
