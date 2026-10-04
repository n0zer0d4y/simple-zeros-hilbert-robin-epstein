# e14: big symmetric configurations with L levels (fractions of N and ratios as in the scan) -> data text via the half-size eigenvector; dtype float64 or float32.
import sys, time, json
import numpy as np
from scipy.sparse.linalg import LinearOperator, eigsh
import e13_make_big as e13
from e10_half import build_M, positions
from e11_opt_half import make_gaps

FR = [0.0219, 0.0078, 0.0027, 0.0009, 0.0003]; RR = [17.9, 9.5, 9.5, 9.5, 9.5]

def cfg(N, f1, g1, L):
    ns = [f1 * N] + [f * N for f in FR][:L - 1]; lr = [np.log(g1 * N)] + [np.log(r) for r in RR][:L - 1]
    return make_gaps(N, L, lr, ns)

def eigen(g, dtype, tol):
    M = build_M(g, dtype); h, c = M.shape
    op = LinearOperator((c, c), matvec=lambda v: M.T @ (M @ v.astype(dtype)), dtype=dtype)
    w, V = eigsh(op, k=1, which="LA", tol=tol)
    sigma = float(np.sqrt(w[0])); e = V[:, 0].astype(np.float64)
    u = (M @ e.astype(dtype)).astype(np.float64) / sigma
    return sigma, e, u

if __name__ == "__main__":
    N = int(sys.argv[1]); f1 = float(sys.argv[2]); g1 = float(sys.argv[3]); L = int(sys.argv[4]); dt = np.float64 if sys.argv[5] == "64" else np.float32
    out = cfg(N, f1, g1, L); g = out[0]
    t0 = time.time(); sigma, e, u = eigen(g, dt, 1e-12 if dt == np.float64 else 1e-8)
    z = e13.full_vector(N, sigma, e, u); lam, d = positions(g)
    w = z * np.sqrt(d); w = w / np.max(np.abs(w)); s = 2.0 ** 44
    a = np.rint(w.real * s).astype(np.int64); b = np.rint(w.imag * s).astype(np.int64)
    with open("data_N%d.txt" % N, "w") as f:
        f.write("%d\n" % N); f.write(" ".join(str(int(x)) for x in g) + "\n"); f.write("\n".join("%d %d" % (x, y) for x, y in zip(a, b)) + "\n")
    print("N =", N, "L =", L, "counts", out[2], "gammas", [int(round(v)) for v in out[1]], "extent", int(g.sum()), "sigma =", repr(sigma), "pi - sigma =", np.pi - sigma, "(%.0fs)" % (time.time() - t0), flush=True)
    json.dump({"N": N, "f1": f1, "g1": g1, "L": L, "counts": out[2], "gammas": out[1], "sigma": sigma, "dtype": sys.argv[5]}, open("data_N%d_meta.json" % N, "w"))
