"""Independent cross-check (method B) for odd_robin_gap.py.

Differences from method A (odd_robin_gap.py), on purpose:
  * pruning bound: elementary. A completion k <= B with primes >= q_j has at most m distinct
    primes, where m = max{m : q_j q_{j+1} ... q_{j+m-1} <= B}, and the i-th smallest prime of k is
    >= q_{j+i}; since sigma(q^e)/q^e < q/(q-1), ln(sigma(k)/k) <= sum_{i<m} ln(q_{j+i}/(q_{j+i}-1)).
    (no Lagrange multipliers anywhere)
  * numerics: mpmath interval arithmetic (iv), exact Fractions for sigma(n)/n, instead of Arb.
  * the candidate set is defined EXACTLY: odd n in [L, U] with sigma(n)/n >= f(L) = (e^gamma/2) loglog L.

Usage: python odd_robin_check_B.py [L] [U]   (defaults: Washington-Yang gap (N, c0))
Prints the candidate list size, the set hash, and any violators. Compare with method A's output.
"""
import sys, math, time, bisect, hashlib
from fractions import Fraction
import mpmath as mp
from mpmath import iv

mp.mp.prec = 300
iv.prec = 300
EPS = 1e-9

def sieve(n):
    s = bytearray([1]) * (n + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i, v in enumerate(s) if v]

PR = [p for p in sieve(20000) if p % 2 == 1]
LNP = [math.log(p) for p in PR]
GAIN = [-math.log1p(-1.0 / p) for p in PR]
CUM = [0.0]
GC = [0.0]
for a, b in zip(LNP, GAIN):
    CUM.append(CUM[-1] + a)
    GC.append(GC[-1] + b)

def ub2(lnB, j):
    """ln of an upper bound for sigma(k)/k, k<=B, all primes of k >= PR[j]."""
    if lnB <= 0 or j >= len(PR):
        return 0.0
    # largest m with CUM[j+m]-CUM[j] <= lnB (+ tiny for rounding)
    target = CUM[j] + lnB + 1e-12
    jm = bisect.bisect_right(CUM, target) - 1      # index such that CUM[jm] <= target
    m_end = min(jm, len(PR))
    return GC[m_end] - GC[j]

def lsig(q, e):
    return math.log1p(-q ** (-(e + 1.0))) - math.log1p(-1.0 / q)

def fmt(fac):
    return "*".join("%d^%d" % (q, e) if e > 1 else "%d" % q for q, e in fac)

def run(L, U):
    f_L = mp.mpf("0.5") * mp.exp(mp.euler) * mp.log(mp.log(mp.mpf(L)))
    R0log = math.log(float(f_L))
    cands = []
    nodes = [0]
    exhausted = [False]
    def rec(j, n, lnr, fac):
        nodes[0] += 1
        if n >= L and lnr >= R0log - EPS:
            cands.append((n, tuple(fac)))
        B = U // n
        if j >= len(PR):
            exhausted[0] = True
            return
        if B < PR[j]:
            return
        lnB = math.log(B)
        if lnr + ub2(lnB, j) < R0log - EPS:
            return
        jj = j
        while jj < len(PR):
            q = PR[jj]
            if q > B:
                return
            if lnr + GAIN[jj] + ub2(lnB - LNP[jj], jj + 1) < R0log - EPS:
                return
            e = 1
            nq = n * q
            while nq <= U:
                fac.append((q, e))
                rec(jj + 1, nq, lnr + lsig(q, e), fac)
                fac.pop()
                e += 1
                nq *= q
            jj += 1
        exhausted[0] = True
    rec(0, 1, 0.0, [])
    return f_L, cands, nodes[0], exhausted[0]

def exact_ratio(fac):
    num = 1
    den = 1
    for q, e in fac:
        num *= (q ** (e + 1) - 1)
        den *= (q ** e) * (q - 1)
    return Fraction(num, den)

def decide(fac, n):
    r = exact_ratio(fac)
    lhs = iv.mpf(r.numerator) / iv.mpf(r.denominator)
    rhs = iv.mpf("0.5") * iv.exp(iv.euler) * iv.log(iv.log(iv.mpf(n)))
    d = lhs - rhs
    if d.a > 0:
        return 1, d
    if d.b < 0:
        return -1, d
    return 0, d

if __name__ == "__main__":
    base = 1
    for q, e in [(3, 4), (5, 3), (7, 2)] + [(p, 1) for p in PR if 11 <= p <= 61]:
        base *= q ** e
    N = base
    c0 = N * 67
    L = int(sys.argv[1]) if len(sys.argv) > 1 else N + 1
    U = int(sys.argv[2]) if len(sys.argv) > 2 else c0 - 1
    t0 = time.time()
    f_L, cands, nodes, exh = run(L, U)
    print("method B: L=%d U=%d  f(L)=%s" % (L, U, mp.nstr(f_L, 15)))
    print("nodes:", nodes, " candidates (ratio>=f(L) by float, EPS-slack):", len(cands), "%.1fs" % (time.time() - t0))
    if exh:
        print("WARNING: prime table exhausted; incomplete")
    # exact filter: keep n whose exact ratio >= f(L) (interval-decided)
    exact = []
    for n, fac in cands:
        r = exact_ratio(fac)
        lhs = iv.mpf(r.numerator) / iv.mpf(r.denominator)
        fl = iv.mpf("0.5") * iv.exp(iv.euler) * iv.log(iv.log(iv.mpf(L)))
        if (lhs - fl).b >= 0:     # not provably below f(L)
            exact.append((n, fac))
    exact.sort()
    h = hashlib.sha256(("\n".join(str(n) for n, _ in exact)).encode()).hexdigest()[:16]
    print("exact candidate set size:", len(exact), " sha256(sorted n)[:16] =", h)
    viol = []
    worst = None
    for n, fac in exact:
        s, d = decide(fac, n)
        if worst is None or d.mid > worst[0]:
            worst = (d.mid, n, fac)
        if s >= 0:
            viol.append((n, fac, s))
    print("violating or undecided:", len(viol))
    for n, fac, s in viol[:30]:
        print("  n=%d [%s] verdict %d" % (n, fmt(fac), s))
    if worst:
        print("largest margin sigma/n - f(n) = %s at n=%d [%s]" % (mp.nstr(worst[0], 10), worst[1], fmt(worst[2])))
    open("candidates_B.txt", "w").write("\n".join("%d %s" % (n, fmt(fac)) for n, fac in exact))
