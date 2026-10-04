# e10: spectral radius of the Montgomery-Vaughan matrix of a REFLECTION-SYMMETRIC configuration via the half-size real matrix M (even-to-odd block):
#   J B J = -B  =>  B = [[0, M], [-M^T, 0]] in the (odd, even) basis ;  rho(B) = sigma_max(M),  M_ik = B_ik + B_ik'  (i, k in the left half, k' = N-1-k; middle column sqrt2 B_im for odd N).
import sys, time, json
import numpy as np
from scipy.sparse.linalg import LinearOperator, eigsh
from scipy.optimize import minimize

def positions(g):
    g = np.asarray(g, dtype=np.float64)
    lam = np.concatenate([[0.0], np.cumsum(g)]); N = len(g) + 1
    d = np.empty(N); d[0] = g[0]; d[-1] = g[-1]; d[1:-1] = np.minimum(g[:-1], g[1:])
    return lam, d

def build_M(g, dtype=np.float32, chunk=1024):
    lam, d = positions(g); N = len(lam); h = N // 2; odd = N % 2
    sq = np.sqrt(d)
    cols = h + odd
    M = np.empty((h, cols), dtype=dtype)
    lam_r = lam[::-1]; sq_r = sq[::-1]
    for i0 in range(0, h, chunk):
        i1 = min(h, i0 + chunk)
        li = lam[i0:i1, None]; si = sq[i0:i1, None]
        A = si * sq[None, :h] / np.where(li == lam[None, :h], 1.0, li - lam[None, :h])          # B_ik, k in left half
        for r in range(i0, i1): A[r - i0, r] = 0.0
        Bk = si * sq_r[None, :h] / (li - lam_r[None, :h])                                       # B_ik' with k' = N-1-k (never equal to i for i, k < N/2 except the middle)
        M[i0:i1, :h] = (A + Bk).astype(dtype)
        if odd:
            M[i0:i1, h] = (np.sqrt(2.0) * si[:, 0] * sq[h] / (lam[i0:i1] - lam[h])).astype(dtype)
    return M

def rho_half(g, tol=1e-7, dtype=np.float32, vec=False):
    M = build_M(g, dtype); h, c = M.shape
    op = LinearOperator((c, c), matvec=lambda v: M.T @ (M @ v.astype(dtype)), dtype=dtype)
    w, V = eigsh(op, k=1, which="LA", tol=tol)
    return (float(np.sqrt(w[0])), V[:, 0]) if vec else float(np.sqrt(w[0]))

def counts(N, L, c1=0.5 * (1 - 1 / np.pi)):
    nj = [max(1, int(round(c1 * np.pi ** (-j) * (N - 1)))) for j in range(1, L + 1)]
    return [N - 1 - 2 * sum(nj)] + nj

def gap_list(n, gam):
    left = []
    for j in range(len(n) - 1, 0, -1): left += [int(max(2, round(gam[j])))] * n[j]
    return np.array(left + [1] * n[0] + left[::-1], dtype=np.int64)

if __name__ == "__main__":
    from e9_dense_arpack import rho_dense
    n = counts(1001, 4); g = gap_list(n, [1.0, 12.7, 150.9, 1450.3, 11957.4])
    t0 = time.time(); a = rho_half(g, dtype=np.float32); t1 = time.time() - t0
    t0 = time.time(); b = rho_half(g, dtype=np.float64, tol=1e-12); t2 = time.time() - t0
    t0 = time.time(); c = rho_dense(g, tol=1e-12); t3 = time.time() - t0
    print("half float32:", a, "(%.2fs)" % t1, " half float64:", b, "(%.2fs)" % t2, " full dense:", c, "(%.2fs)" % t3)
    n = counts(1000, 4); g = gap_list(n, [1.0, 12.7, 150.9, 1450.3, 11957.4])    # even N
    print("even N =", len(g) + 1, "half:", rho_half(g, dtype=np.float64, tol=1e-12), " full:", rho_dense(g, tol=1e-12))
