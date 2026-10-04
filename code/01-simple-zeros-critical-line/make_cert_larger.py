"""Re-run the fast larger-cell certificates (H = 7: k = 3, 4, 5; H = 8: k = 3, 4, 5) if their summaries are missing, and
assemble certificates/01-simple-zeros-critical-line/cells-H7-H8.json from all bnbk_H*_k*.json outputs, the 1-D check of the
minorant and the exact-arithmetic envelope.

The slower certificates are run separately:
    python bnbk.py 7 6 0.0030683              (about a minute)
    python bnbk.py 8 6 0.0015534              (a few minutes)
    python run_h8_k7.py 0.00375               (six-dimensional, about 23 minutes on one core)
    python oned_check.py targets-H7-H8.json   (the 40 lines below K_0^2)

Run from this folder: python make_cert_larger.py targets-H7-H8.json
"""
import sys, json, glob, os
from fractions import Fraction as F
import bnbk, envelope

targets_path = sys.argv[1] if len(sys.argv) > 1 else "targets-H7-H8.json"
targets = json.load(open(targets_path, encoding="utf-8"))
fast = [("7", 3, "0.0000113307"), ("7", 4, "0.000143197"), ("7", 5, "0.000752866"),
        ("8", 3, "0.00000643552"), ("8", 4, "0.0000705725"), ("8", 5, "0.000491377")]
for H, k, tau in fast:
    name = "bnbk_H%s_k%d_tau%s.json" % (H, k, tau)
    if not os.path.exists(name):
        r = bnbk.certify(F(H), k, F(tau), n0=8, max_level=26, verbose=False)
        json.dump(r, open(name, "w"), indent=1)
        print("certified", H, k, tau, r["cells_evaluated"], "cells")
runs = {}
for f in sorted(glob.glob("bnbk_H*_k*_tau*.json")):
    r = json.load(open(f))
    runs[f] = {k: r[k] for k in ("H", "k", "tau", "n0", "cells_evaluated", "cells_dropped", "max_level", "min_dropped_lb", "seconds", "certified")}
oned = json.load(open("oned_check.out.json"))
lines = targets["phi_lines"]
phi1 = envelope.phi_at(lines, F(1))
out = {
    "id": "cells-H7-H8",
    "method": "feasibility branch and bound, python-flint balls (128 bits), local enclosures of (K_0^2)'' over each cell (bnbk.py, kernel2.py); targets 0.97 times the best values of a structured global search (targets-H7-H8.json)",
    "minima_certified": runs,
    "one_dimensional_check": {"statement": "each of the 40 lines a_i + m_i g lies below K_0(g)^2 on [0, 1.06] and is non-positive at g >= 1.06", **oned},
    "phi_at_1": str(float(phi1)),
    "envelope_exact_arithmetic": {},
    "H7_line": {"s": "12194/10^7", "t": "45914/10^7", "K": 8, "base_cases": "k = 4, 5 from P_4(7), P_5(7); k = 6, 7 from P_6(7) (Psi_7 >= Psi_6); k <= 3 trivial (line negative); anchor Psi_8 >= 14 phi(1)"},
    "H8_line": {"s": "21240/10^7", "t": "96373/10^7", "K": 9, "base_cases": "k = 5, 6 from P_5(8), P_6(8); k = 7, 8 from P_7(8) >= 0.00375 (Psi_8 >= Psi_7); k <= 4 trivial (line negative); anchor Psi_9 >= 16 phi(1)"},
    "final_constants": "final_constants.py (python-flint, 256 bits); output final_constants.out.txt",
    "ceiling": "own-code ball arithmetic; Wang's published inputs not re-derived; a proportion of simple zeros says nothing about RH",
}
for plan in targets["plans"]:
    H = F(str(plan["H"])); K = int(plan["anchor_K"])
    p = {int(k): F(str(v)) for k, v in plan["targets_P_k"].items()}
    (u, s, t), tau = envelope.best_line(H, p, K, 2 * (K - 1) * phi1)
    out["envelope_exact_arithmetic"]["H=%s" % plan["H"]] = {"best_s": float(s), "best_t": float(t), "bound": float(u),
        "distinct": float((1 + envelope.C0_LOW) / 2 + (s * u - t / H) / 2), "tau_star": [float(x) for x in tau]}
dest = "../../certificates/01-simple-zeros-critical-line/cells-H7-H8.json"
json.dump(out, open(dest, "w", encoding="utf-8"), indent=1, ensure_ascii=False)
print("written", dest, "with", len(runs), "runs")
