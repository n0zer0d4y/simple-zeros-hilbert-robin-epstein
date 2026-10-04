"""Odd Robin inequality: decade-by-decade exhaustive scan beyond the Washington-Yang gap.

For each decade [10^k, 10^(k+1)) (starting at L0 = N+1 for the first segment) enumerates ALL odd n
with sigma(n)/n >= f(L_seg) (method A of odd_robin_gap.py: Lagrangian-pruned DFS), decides every
candidate with Arb ball arithmetic, and records the closest approach to violation
    margin(n) = sigma(n)/n - (e^gamma/2) loglog n   (negative = inequality holds).
Any violator in a segment would be printed; under RH there is none beyond N.

Usage: python odd_robin_scan.py [k_max]
"""
import sys, time, math, json
import flint
from flint import arb, fmpz
import odd_robin_gap as A

kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 60
base = fmpz(1)
for q, e in [(3, 4), (5, 3), (7, 2)] + [(p, 1) for p in A.PR if 11 <= p <= 61]:
    base *= fmpz(q) ** e
N = int(base)

rows = []
viol_total = 0
t_all = time.time()
segs = []
lo = N + 1
k = 28
while k <= kmax:
    hi = 10 ** k - 1
    if hi >= lo:
        segs.append((lo, hi))
    lo = 10 ** k
    k += 1
for (L, U) in segs:
    t0 = time.time()
    flint.ctx.prec = 300
    fL = arb(0.5) * arb.const_euler().exp() * arb(L).log().log()
    R0log = math.log(float(fL.mid()))
    cands, nodes = A.search(L, U, R0log)
    best = None
    nv = 0
    ncand = 0
    for fac, n, lnr in cands:
        r = A.sigma_over(fac)
        if (arb(r.p) / arb(r.q) - fL).upper() < 0:
            continue                      # provably below f(L) <= f(n): satisfied, not a candidate
        ncand += 1
        s, d = A.decide(fac)
        if s >= 0:
            nv += 1
            print("   VIOLATOR/UNDECIDED:", n, A.fmt(fac), s, d.str(10, radius=False))
        m = float(d.mid())
        if best is None or m > best[0]:
            best = (m, int(n), A.fmt(fac))
    viol_total += nv
    rows.append(dict(L=str(L), U=str(U), nodes=nodes, candidates=ncand, violators=nv,
                     best_margin=None if best is None else best[0],
                     best_n=None if best is None else str(best[1]),
                     best_fac=None if best is None else best[2]))
    print("[%s, %s]  nodes=%d cands=%d violators=%d  best margin=%s  %.1fs" % (
        str(L)[:12] + "..", "1e%d" % round(math.log10(U + 1)), nodes, ncand, nv,
        None if best is None else "%.6f" % best[0], time.time() - t0), flush=True)
print("total violators in (N, 1e%d):" % kmax, viol_total, " total %.1fs" % (time.time() - t_all))
json.dump(rows, open("scan.json", "w"), indent=1)
