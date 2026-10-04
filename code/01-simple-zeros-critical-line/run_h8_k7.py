"""Background run: P_7(8) >= tau (6-D) with the general ball branch and bound; one worker, progress log."""
import sys, time, json
from fractions import Fraction
import bnbk
tau = sys.argv[1] if len(sys.argv) > 1 else "0.00375"
budget = int(sys.argv[2]) if len(sys.argv) > 2 else 80_000_000
t0 = time.time()
try:
    r = bnbk.certify(Fraction(8), 7, Fraction(tau), n0=8, max_level=26, max_cells=budget, log_every=2_000_000)
    print("CERTIFIED", json.dumps({k: v for k, v in r.items() if k != "per_level"}), flush=True)
    json.dump(r, open("bnbk_H8_k7_tau%s.json" % tau, "w"), indent=1)
except RuntimeError as e:
    print("FAILED", str(e)[:300], "t=%.0fs" % (time.time() - t0), flush=True)
