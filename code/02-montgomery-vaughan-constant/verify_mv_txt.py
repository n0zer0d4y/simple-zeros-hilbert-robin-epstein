#!/usr/bin/env python
# Independent verifier for the text data format of mvcert.c (N; N-1 gaps; N lines "a b"): python-flint only, no C.
# method A: exact integer cross-correlation (needs extent R small enough for a polynomial of R+1 coefficients); method B: arb dot product over all pairs (O(N^2) Python loop).
import sys, time
from flint import fmpz_poly, arb, ctx, fmpq

def load(path):
    toks = open(path).read().split(); N = int(toks[0]); g = [int(x) for x in toks[1:N]]
    rest = toks[N:]; a = [int(rest[2 * i]) for i in range(N)]; b = [int(rest[2 * i + 1]) for i in range(N)]
    return g, a, b

def deltas(g):
    N = len(g) + 1; d = [0] * N; d[0] = g[0]; d[-1] = g[-1]
    for j in range(1, N - 1): d[j] = min(g[j - 1], g[j])
    return d

def method_A(g, a, b):
    N = len(g) + 1; lam = [0]
    for x in g: lam.append(lam[-1] + x)
    R = lam[-1]; Bc = [0] * (R + 1); Ar = [0] * (R + 1)
    for m in range(N): Bc[lam[m]] = b[m]; Ar[R - lam[m]] = a[m]
    co = (fmpz_poly(Bc) * fmpz_poly(Ar)).coeffs()
    T = arb(0)
    for dd in range(1, R + 1):
        diff = (int(co[R + dd]) if R + dd < len(co) else 0) - (int(co[R - dd]) if R - dd >= 0 and R - dd < len(co) else 0)
        if diff: T += arb(diff) / dd
    return T

def method_B(g, a, b):
    N = len(g) + 1; lam = [0]
    for x in g: lam.append(lam[-1] + x)
    av = [arb(x) for x in a]; T = arb(0)
    for m in range(N):
        s = arb(0); lm = lam[m]
        for n in range(N):
            if n != m: s += av[n] / (lm - lam[n])
        T += arb(b[m]) * s
    return T

if __name__ == "__main__":
    ctx.prec = 300
    g, a, b = load(sys.argv[1]); mode = sys.argv[2]; N = len(g) + 1
    d = deltas(g); den = fmpq(0)
    for m in range(N): den += fmpq(a[m] ** 2 + b[m] ** 2, d[m])
    denA = arb(den.p) / arb(den.q); t0 = time.time()
    T = method_A(g, a, b) if mode == "A" else method_B(g, a, b)
    ratio = 2 * abs(T) / denA
    print("N = %d method %s: ratio in %s  (pi + %s) [%.0fs]" % (N, mode, ratio.str(28, radius=False), (ratio - arb.pi()).str(8, radius=False), time.time() - t0), flush=True)
