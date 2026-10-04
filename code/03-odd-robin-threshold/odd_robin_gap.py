"""Odd Robin inequality: exhaustive search for violators in a range (Washington-Yang gap).

Washington-Yang (arXiv:2008.04787): RH <=> sigma(n) < (e^gamma/2) n loglog n for all odd
n >= c0 = 3^4 5^3 7^2 11 ... 67, and N = c0/67 (primes 3..61) is the last odd colossally
abundant violator they found. They write: "We do not know whether the inequality is
satisfied for N < n < c0".

This script decides it exactly. A VIOLATOR is an odd n with sigma(n)/n >= f(n) := (e^gamma/2) loglog n.
Because f is increasing, every violator n >= L has sigma(n)/n >= R0 := f(L).
We enumerate ALL odd n <= U with sigma(n)/n >= R0 by depth-first search over factorisations
(primes in increasing order, exponents >= 1, gaps allowed), pruned by a rigorous bound:

  for any lambda >= 0, any completion k <= B using primes >= q_j satisfies
     ln(sigma(k)/k) <= lambda ln B + sum_{q >= q_j} max_{e >= 0} [ln(sigma(q^e)/q^e) - lambda e ln q]
  (Lagrangian relaxation; the same optimisation that defines colossally abundant numbers).

Pruning uses float64 with a safety margin; every reported candidate is then decided with
python-flint ball arithmetic (rigorous). Completeness of the enumeration rests on the bound above
(pure inequality) and on the float margin EPS.

Usage: python odd_robin_gap.py [L] [U] [R0_slack]
"""
import sys, math, time
import flint
from flint import arb, fmpz, fmpq

EPS = 1e-9          # safety margin on pruning (relative, in ln-ratio)

def sieve(n):
    s = bytearray([1]) * (n + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i, v in enumerate(s) if v]

PR = [p for p in sieve(20000) if p % 2 == 1]
LN = [math.log(p) for p in PR]

def lsig(q, e):
    """ln(sigma(q^e)/q^e), stable."""
    # sigma(q^e)/q^e = (1 - q^-(e+1)) / (1 - 1/q)
    return math.log1p(-q ** (-(e + 1.0))) - math.log1p(-1.0 / q) if e > 0 else 0.0

# lambda grid and suffix sums of per-prime maxima
# lambda >= 1e-4 only: for such lambda a prime q contributes (g > 0) only if 1/q > lambda ln q,
# i.e. q < ~1100, far inside the table (20000), so the suffix sums are the TRUE sums over all primes.
LAMS = [10 ** (-k / 5.0) for k in range(0, 26)]       # 1 .. 1e-5  (q < 1/(1e-5 ln q) ~ 1.1e4 < 20000)
def g(q, lq, lam):
    best = 0.0
    e = 1
    while True:
        val = lsig(q, e) - lam * e * lq
        if val > best:
            best = val
        # increments shrink geometrically; stop when gain per extra exponent < cost
        if lsig(q, e + 1) - lsig(q, e) < lam * lq or e > 60:
            break
        e += 1
    return best

SUF = []
for lam in LAMS:
    s = [0.0] * (len(PR) + 1)
    for j in range(len(PR) - 1, -1, -1):
        s[j] = s[j + 1] + g(PR[j], LN[j], lam)
    SUF.append(s)

def ub_log(lnB, j):
    """rigorous (up to float rounding) upper bound on ln(sigma(k)/k), k<=B, primes of k >= PR[j]."""
    if lnB <= 0:
        return 0.0
    best = 1e18
    for lam, s in zip(LAMS, SUF):
        v = lam * lnB + s[j]
        if v < best:
            best = v
    return best

def sigma_over(n_fac):
    num = fmpz(1)
    den = fmpz(1)
    for q, e in n_fac:
        num *= (fmpz(q) ** (e + 1) - 1)
        den *= (fmpz(q) ** e) * (q - 1)
    return fmpq(num, den)

def value(n_fac):
    n = fmpz(1)
    for q, e in n_fac:
        n *= fmpz(q) ** e
    return n

EG2 = None

def decide(n_fac, prec=300):
    """rigorous: returns +1 if sigma(n)/n > f(n), -1 if <, 0 undecided."""
    flint.ctx.prec = prec
    n = value(n_fac)
    r = sigma_over(n_fac)
    lhs = arb(r.p) / arb(r.q)
    nn = arb(n)
    rhs = arb(0.5) * arb.const_euler().exp() * nn.log().log()
    d = lhs - rhs
    if d.lower() > 0:
        return 1, d
    if d.upper() < 0:
        return -1, d
    return 0, d

def search(L, U, R0log):
    lnU = math.log(U)
    out = []
    nodes = [0]
    exhausted = [False]
    def dfs(fac, n, lnr, j0):
        nodes[0] += 1
        if n >= L and lnr >= R0log - EPS:
            out.append((list(fac), n, lnr))
        B = U // n
        if B < PR[j0]:
            return
        lnB = math.log(B)
        j = j0
        while j < len(PR):
            q = PR[j]
            if q > B:
                break
            # best case for ANY exponent at this prime: gain <= q/(q-1), budget <= B/q
            gmax = -math.log1p(-1.0 / q)
            if lnr + gmax + ub_log(lnB - LN[j], j + 1) < R0log - EPS:
                break   # monotone in j: no later prime can work
            nq = n * q
            e = 1
            qe = q
            while nq <= U:
                lnr2 = lnr + lsig(q, e)
                lnB2 = math.log(U / nq)
                if lnr2 + ub_log(lnB2, j + 1) >= R0log - EPS:
                    fac.append((q, e))
                    dfs(fac, nq, lnr2, j + 1)
                    fac.pop()
                e += 1
                nq *= q
            j += 1
        else:
            exhausted[0] = True   # ran off the prime table without the monotone break
    dfs([], 1, 0.0, 0)
    if exhausted[0]:
        print("WARNING: prime table exhausted in some branch; enumeration may be incomplete")
    return out, nodes[0]

def fmt(fac):
    return "*".join("%d^%d" % (q, e) if e > 1 else "%d" % q for q, e in fac)

if __name__ == "__main__":
    # defaults: the Washington-Yang gap
    prod61 = fmpz(1)
    for q, e in [(3, 4), (5, 3), (7, 2)] + [(p, 1) for p in PR if 11 <= p <= 61]:
        prod61 *= fmpz(q) ** e
    N = int(prod61)
    c0 = N * 67
    L = int(sys.argv[1]) if len(sys.argv) > 1 else N + 1
    U = int(sys.argv[2]) if len(sys.argv) > 2 else c0 - 1
    flint.ctx.prec = 200
    Ls = arb(L)
    f_L = 0.5 * arb.const_euler().exp() * Ls.log().log()
    slack = float(sys.argv[3]) if len(sys.argv) > 3 else 0.0
    R0log = math.log(float(f_L.mid())) - slack
    print("N  =", N, "=", "3^4*5^3*7^2*11*...*61")
    print("c0 =", c0)
    fac_N = [(3, 4), (5, 3), (7, 2)] + [(p, 1) for p in PR if 11 <= p <= 61]
    s, d = decide(fac_N)
    print("N violates odd Robin:", s, " margin sigma/n - f(n) =", d.str(15, radius=False))
    print("search range [L,U] = [%d, %d]; R0 = f(L) = %s" % (L, U, f_L.str(15, radius=False)))
    t0 = time.time()
    cands, nodes = search(L, U, R0log)
    print("nodes visited:", nodes, " candidates n>=L with sigma/n >= R0:", len(cands), " %.1fs" % (time.time() - t0))
    # exact candidate set: keep n whose exact ratio is not provably below f(L)  (same definition as method B)
    import hashlib
    flint.ctx.prec = 300
    fL = arb(0.5) * arb.const_euler().exp() * arb(L).log().log()
    exact = []
    for fac, n, lnr in cands:
        r = sigma_over(fac)
        if (arb(r.p) / arb(r.q) - fL).upper() >= 0:
            exact.append((int(n), fac))
    exact.sort()
    h = hashlib.sha256(("\n".join(str(n) for n, _ in exact)).encode()).hexdigest()[:16]
    print("exact candidate set size:", len(exact), " sha256(sorted n)[:16] =", h)
    open("candidates_A.txt", "w").write("\n".join("%d %s" % (n, fmt(fac)) for n, fac in exact))
    viol = []
    for fac, n, lnr in cands:
        s, d = decide(fac)
        if s >= 0:
            viol.append((n, fac, s, d))
    print("candidates decided violating or undecided:", len(viol))
    for n, fac, s, d in sorted(viol)[:50]:
        print("  n=%d  [%s]  verdict=%s  margin=%s" % (n, fmt(fac), s, d.str(10, radius=False)))
    if cands:
        best = max(cands, key=lambda t: t[2])
        s, d = decide(best[0])
        print("max ratio candidate:", fmt(best[0]), "verdict", s, "margin", d.str(10, radius=False))
    # closest-to-violating candidates (largest margins), for the record
    scored = []
    for fac, n, lnr in cands:
        s, d = decide(fac)
        scored.append((float(d.mid()), n, fac))
    scored.sort(reverse=True)
    print("top margins (sigma/n - f(n)), most violating first:")
    for m, n, fac in scored[:12]:
        print("  %+.10f  n=%d  [%s]" % (m, n, fmt(fac)))
