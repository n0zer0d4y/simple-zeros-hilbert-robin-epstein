"""Robin-type inequality for integers coprime to the first k primes (k = 0: Robin; k = 1: odd).

Violator of level k:  n >= 3 coprime to p_1..p_k with
    sigma(n)/n >= C_k loglog n,   C_k = e^gamma * prod_{i<=k} (1 - 1/p_i).
(k = 0 is Robin's inequality: the exceptions are the 27 numbers up to 5040; k = 1 is the odd inequality
of Washington-Yang.)  Method A of odd_robin_gap.py generalised: depth-first search over factorisations
into the allowed primes, pruned by the Lagrangian bound
    ln(sigma(m)/m) <= lam ln B + sum_{q >= q_j allowed} max_e [ln(sigma(q^e)/q^e) - lam e ln q],
every candidate decided with Arb ball arithmetic, over geometric segments.

Usage: python coprime_robin.py k jmax [jmin]
  scans segments [10^j, 10^(j+1)) for j = jmin..jmax-1 (default jmin = 0, with n >= 3).
Prints, per segment, #candidates, #violators, the largest violator, and the closest approach.
"""
import sys, math, time, json
import flint
from flint import arb, fmpz, fmpq

EPS = 1e-9

def sieve(n):
    s = bytearray([1]) * (n + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i, v in enumerate(s) if v]

ALLP = sieve(20000)

def lsig(q, e):
    return math.log1p(-q ** (-(e + 1.0))) - math.log1p(-1.0 / q) if e > 0 else 0.0

class Ctx:
    def __init__(self, k):
        self.k = k
        self.PR = ALLP[k:]
        self.LN = [math.log(p) for p in self.PR]
        self.LAMS = [10 ** (-i / 5.0) for i in range(0, 26)]   # 1 .. 1e-5
        self.SUF = []
        for lam in self.LAMS:
            s = [0.0] * (len(self.PR) + 1)
            for j in range(len(self.PR) - 1, -1, -1):
                s[j] = s[j + 1] + self._g(self.PR[j], self.LN[j], lam)
            self.SUF.append(s)
        flint.ctx.prec = 300
        c = arb.const_euler().exp()
        for p in ALLP[:k]:
            c = c * (arb(1) - arb(1) / p)
        self.C = c                       # C_k as a ball

    @staticmethod
    def _g(q, lq, lam):
        best = 0.0
        e = 1
        while True:
            val = lsig(q, e) - lam * e * lq
            if val > best:
                best = val
            if lsig(q, e + 1) - lsig(q, e) < lam * lq or e > 80:
                break
            e += 1
        return best

    def ub(self, lnB, j):
        if lnB <= 0:
            return 0.0
        return min(lam * lnB + s[j] for lam, s in zip(self.LAMS, self.SUF))

def sigma_over(fac):
    num = fmpz(1); den = fmpz(1)
    for q, e in fac:
        num *= (fmpz(q) ** (e + 1) - 1)
        den *= (fmpz(q) ** e) * (q - 1)
    return fmpq(num, den)

def value(fac):
    n = fmpz(1)
    for q, e in fac:
        n *= fmpz(q) ** e
    return n

def margin(ctx, fac, prec=300):
    """ball for sigma(n)/n - C_k loglog n"""
    flint.ctx.prec = prec
    n = value(fac)
    r = sigma_over(fac)
    return arb(r.p) / arb(r.q) - ctx.C * arb(n).log().log()

def search(ctx, L, U, R0log):
    PR, LN = ctx.PR, ctx.LN
    out = []
    nodes = [0]
    exhausted = [False]
    def dfs(fac, n, lnr, j0):
        nodes[0] += 1
        if n >= L and lnr >= R0log - EPS:
            out.append((list(fac), n, lnr))
        B = U // n
        if j0 >= len(PR):
            exhausted[0] = True
            return
        if B < PR[j0]:
            return
        lnB = math.log(B)
        j = j0
        while j < len(PR):
            q = PR[j]
            if q > B:
                return
            gmax = -math.log1p(-1.0 / q)
            if lnr + gmax + ctx.ub(lnB - LN[j], j + 1) < R0log - EPS:
                return
            nq = n * q
            e = 1
            while nq <= U:
                lnr2 = lnr + lsig(q, e)
                if lnr2 + ctx.ub(math.log(U / nq), j + 1) >= R0log - EPS:
                    fac.append((q, e))
                    dfs(fac, nq, lnr2, j + 1)
                    fac.pop()
                e += 1
                nq *= q
            j += 1
        exhausted[0] = True
    dfs([], 1, 0.0, 0)
    if exhausted[0]:
        print("WARNING: prime table exhausted")
    return out, nodes[0]

def fmt(fac):
    return "*".join("%d^%d" % (q, e) if e > 1 else "%d" % q for q, e in fac) if fac else "1"

if __name__ == "__main__":
    k = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    jmax = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    jmin = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    ctx = Ctx(k)
    print("k=%d  excluded primes %s  C_k = %s" % (k, ALLP[:k], ctx.C.str(15, radius=False)))
    t_all = time.time()
    rows = []
    allviol = []
    for j in range(jmin, jmax):
        L = max(3, 10 ** j)
        U = 10 ** (j + 1) - 1
        flint.ctx.prec = 300
        fL = ctx.C * arb(L).log().log()
        # for tiny L loglog L can be <= 0: then every n qualifies; use R0 = 0 floor
        R0 = float(fL.mid())
        R0log = math.log(R0) if R0 > 1.0 else 0.0
        cands, nodes = search(ctx, L, U, R0log)
        viol = []
        best = None
        for fac, n, lnr in cands:
            d = margin(ctx, fac)
            if d.upper() >= 0:          # violating or undecided
                viol.append((int(n), fac, d))
            m = float(d.mid())
            if best is None or m > best[0]:
                best = (m, int(n), fac)
        allviol += [(n, fmt(f)) for n, f, d in viol]
        bigv = max(viol, key=lambda t: t[0]) if viol else None
        rows.append(dict(j=j, cands=len(cands), viol=len(viol), largest_violator=None if not bigv else str(bigv[0])))
        print("[1e%d,1e%d) nodes=%d cands=%d violators=%d  largest violator=%s  closest margin=%s" % (
            j, j + 1, nodes, len(cands), len(viol),
            "-" if not bigv else "%d [%s]" % (bigv[0], fmt(bigv[1])),
            "-" if best is None else "%+.6f" % best[0]), flush=True)
    allviol.sort()
    print("TOTAL violators:", len(allviol), " largest:", allviol[-1] if allviol else None, " %.1fs" % (time.time() - t_all))
    if len(allviol) <= 60:
        print("all violators:", [n for n, f in allviol])
    json.dump(dict(k=k, jmax=jmax, jmin=jmin, rows=rows, violators=[[str(n), f] for n, f in allviol]),
              open("coprime_k%d_%d.json" % (k, jmax), "w"))
