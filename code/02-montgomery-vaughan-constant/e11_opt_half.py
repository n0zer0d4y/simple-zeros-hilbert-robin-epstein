# e11: structure optimisation with the half-size symmetric operator (float32): parameters log r_j (gamma_j = gamma_{j-1} r_j, gamma_0 = 1) and counts n_j (j >= 1), n_0 = N - 1 - 2 sum n_j.
import sys, time, json
import numpy as np
from scipy.optimize import differential_evolution, minimize
from e10_half import rho_half

def make_gaps(N, L, lr, ns):
    ns = [max(1, int(round(x))) for x in ns]
    n0 = N - 1 - 2 * sum(ns)
    if n0 < 2: return None
    gam = [1.0]
    for j in range(L): gam.append(gam[-1] * np.exp(lr[j]))
    left = []
    for j in range(L, 0, -1): left += [int(max(2, round(gam[j])))] * ns[j - 1]
    return np.array(left + [1] * n0 + left[::-1], dtype=np.int64), gam, ns

def objective(x, N, L):
    out = make_gaps(N, L, x[:L], np.exp(x[L:]))
    if out is None: return 10.0
    g = out[0]
    try: return -rho_half(g, tol=1e-6)
    except Exception: return 10.0

if __name__ == "__main__":
    N = int(sys.argv[1]); L = int(sys.argv[2]); seed = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    gens = int(sys.argv[4]) if len(sys.argv) > 4 else 40
    c1 = 0.5 * (1 - 1 / np.pi)
    ns0 = [c1 * np.pi ** (-j) * (N - 1) for j in range(1, L + 1)]
    bounds = [(np.log(1.5), np.log(2000.0))] * L + [(np.log(max(1.0, 0.25 * n)), np.log(max(2.0, 3.0 * n))) for n in ns0]
    t0 = time.time()
    res = differential_evolution(objective, bounds, args=(N, L), seed=seed, popsize=12, maxiter=gens, tol=1e-9, polish=False, init="sobol")
    x = res.x
    res2 = minimize(objective, x, args=(N, L), method="Nelder-Mead", options={"maxiter": 200, "xatol": 1e-3, "fatol": 1e-10})
    if res2.fun < res.fun: x = res2.x
    g, gam, ns = make_gaps(N, L, x[:L], np.exp(x[L:]))
    c = rho_half(g, tol=1e-9, dtype=np.float64)
    eq = rho_half(np.ones(N - 1, dtype=np.int64), tol=1e-9, dtype=np.float64)
    print("N =", N, "L =", L, "n_j =", ns, "gammas =", [round(v, 1) for v in gam], "C =", round(c, 6), "eq =", round(eq, 6), "pi - C =", round(np.pi - c, 6), "N(pi-C) =", round(N * (np.pi - c), 2), "(%.0fs)" % (time.time() - t0), flush=True)
    json.dump({"N": N, "L": L, "x": list(map(float, x)), "gaps_head": [int(v) for v in g[:5]], "C": c, "ns": ns, "gam": gam}, open("opt_half_N%d_L%d.json" % (N, L), "w"))
