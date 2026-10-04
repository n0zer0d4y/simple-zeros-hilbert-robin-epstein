# e13: eigenvector of a reflection-symmetric configuration from the half-size matrix (float64), converted to Gaussian-integer weights; writes the text input of mvcert.c.
#   M e = sigma u (e even-basis right singular vector, u odd-basis left singular vector):  z = [u ; i e] satisfies B z = i sigma z ;
#   z_j = (u_j + i e_j)/sqrt2 and z_{N-1-j} = (-u_j + i e_j)/sqrt2 for j < N/2, z_mid = i e_mid ;  w_m = sqrt(delta_m) z_m.
import sys, time, json
import numpy as np
from scipy.sparse.linalg import LinearOperator, eigsh
from e10_half import build_M, positions

def eigen_big(g, tol=1e-12):
    M = build_M(g, np.float64); h, c = M.shape
    op = LinearOperator((c, c), matvec=lambda v: M.T @ (M @ v), dtype=np.float64)
    w, V = eigsh(op, k=1, which="LA", tol=tol)
    sigma = float(np.sqrt(w[0])); e = V[:, 0]; u = (M @ e) / sigma
    return sigma, e, u

def full_vector(N, sigma, e, u):
    h = N // 2; odd = N % 2
    z = np.zeros(N, dtype=complex)
    for j in range(h):
        z[j] = (u[j] + 1j * e[j]) / np.sqrt(2); z[N - 1 - j] = (-u[j] + 1j * e[j]) / np.sqrt(2)
    if odd: z[h] = 1j * e[h]
    return z

def write_data(g, path, scale_bits=44, tol=1e-12):
    N = len(g) + 1
    sigma, e, u = eigen_big(g, tol)
    z = full_vector(N, sigma, e, u)
    lam, d = positions(g)
    w = z * np.sqrt(d); w = w / np.max(np.abs(w))
    s = 2.0 ** scale_bits
    a = np.rint(w.real * s).astype(np.int64); b = np.rint(w.imag * s).astype(np.int64)
    with open(path, "w") as f:
        f.write("%d\n" % N); f.write(" ".join(str(int(x)) for x in g) + "\n")
        f.write("\n".join("%d %d" % (x, y) for x, y in zip(a, b)) + "\n")
    return sigma

if __name__ == "__main__":
    from e12_scan import config
    N = int(sys.argv[1]); f1 = float(sys.argv[2]); g1 = float(sys.argv[3]); L = int(sys.argv[4])
    out = config(N, f1, g1, L); g = out[0]
    t0 = time.time(); sigma = write_data(g, "data_N%d.txt" % N)
    print("N =", N, "L =", L, "counts", out[2], "gammas", [int(round(v)) for v in out[1]], "extent", int(g.sum()), "float sigma =", repr(sigma), "pi - sigma =", np.pi - sigma, "(%.0fs)" % (time.time() - t0))
    json.dump({"N": N, "f1": f1, "g1": g1, "L": L, "counts": out[2], "gammas": out[1], "sigma": sigma}, open("data_N%d_meta.json" % N, "w"))
