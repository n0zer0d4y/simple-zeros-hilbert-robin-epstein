# Reproducing the results

## Environment

- **Python 3.12** with the versions in `requirements.txt` (python-flint 0.8.0, mpmath 1.3.0, numpy 2.4.2, scipy 1.17.1, sympy 1.14.0).
- **A C compiler with libquadmath** (gcc) for `mvcert.c`.
- **Lean** v4.28.0 with Mathlib v4.28.0, pinned in `lean/lean-toolchain` and `lean/lakefile.toml`.
- **Working directory.** Every script is run from its own folder under `code/`. Outputs are written next to the script.

## Lean (results 1 and 3)

```
cd lean
lake exe cache get        # downloads prebuilt Mathlib
lake build
lake env lean AxiomCheck.lean
```

`AxiomCheck.lean` prints the axioms of every main theorem and witness. Each must be among `propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx` and no `Lean.ofReduceBool`. On Windows, `scripts/setup-shared-deps.ps1` can point `.lake/packages` at a shared Mathlib store instead.

## Result 1: simple zeros on the critical line

All scripts are in `code/01-simple-zeros-critical-line/`.

| What                               | Command                                                                                                 | Time                       |
| ---------------------------------- | ------------------------------------------------------------------------------------------------------- | -------------------------- |
| m(4) ≥ 0.000221935                 | `python bnb.py m3 4 0.000221935 200`                                                                    | seconds                    |
| P₄(4) ≥ 0.002116538                | `python bnb.py p4 4 0.002116538 64`                                                                     | about a minute             |
| P₄(4) ≥ 0.0009                     | `python bnb.py p4 4 0.0009 48`                                                                          | seconds                    |
| P\_k(7), P\_k(8) for k = 3, 4, 5     | `python make_cert_larger.py targets-H7-H8.json` (runs any missing ones, then assembles the certificate) | seconds each               |
| P₆(7) ≥ 0.0030683                  | `python bnbk.py 7 6 0.0030683`                                                                          | about a minute             |
| P₆(8) ≥ 0.0015534                  | `python bnbk.py 8 6 0.0015534`                                                                          | a few minutes              |
| P₇(8) ≥ 0.00375                    | `python run_h8_k7.py 0.00375`                                                                           | about 23 minutes, one core |
| φ ≤ K₀² (40 lines)                 | `python oned_check.py targets-H7-H8.json`                                                               | seconds                    |
| lines, base cases, final constants | `python final_constants.py`                                                                             | instant                    |
| best lines in exact arithmetic     | `python envelope.py targets-H7-H8.json`                                                                 | seconds                    |

- **Outputs.** Each certificate run writes a JSON summary (`bnb_*.json`, `bnbk_*.json`) whose `certified` field must be `true`. The summaries from our runs are included.
- **Assembled certificates.** These are `certificates/01-simple-zeros-critical-line/cells-H4.json` and `cells-H7-H8.json`.

## Result 2: the Montgomery–Vaughan constant

Scripts are in `code/02-montgomery-vaughan-constant/`, data in `certificates/02-montgomery-vaughan-constant/data/`.

```
gcc -O2 -o mvcert mvcert.c -lquadmath
./mvcert ../../certificates/02-montgomery-vaughan-constant/data/data_N60001.txt          # about five minutes
python verify_mv_txt.py ../../certificates/02-montgomery-vaughan-constant/data/data_N3201.txt A    # exact integer correlation, seconds
python verify_mv_txt.py ../../certificates/02-montgomery-vaughan-constant/data/data_N60001.txt B   # balls over all pairs, about 20 minutes
python e14_big.py 60001 0.11 0.045 4 32    # regenerates a data file (needs several GB of memory)
```

`verify_N*_B.out` hold our ball-arithmetic outputs. The data format is: N; then the N − 1 integer gaps; then N lines `a_m b_m` (the weights w\_m = a\_m + i b\_m).

## Result 3: the odd Robin threshold

Scripts are in `code/03-odd-robin-threshold/`.

```
python odd_robin_gap.py          # method A (python-flint); writes candidates_A.txt, about a minute
python odd_robin_check_B.py      # method B (mpmath intervals); writes candidates_B.txt
python margins.py                # the three decisive margins at 120 digits
python odd_robin_scan.py 60      # decades up to 1e60
python coprime_robin.py 1 120    # all odd violators below 1e120 (k = 1); k = 0 reproduces Robin's exceptions
```

`candidates_A.txt` and `candidates_B.txt` must be identical (1098 lines). Their sorted list has SHA-256 prefix `4bf6339dd6b9b139`.

## Result 4: the Epstein conjecture

Scripts are in `code/04-epstein-conjecture/`.

```
python epstein_arb.py      # Arb enclosures from the definition and from the Bessel series (writes epstein_arb.json)
python epstein_check.py    # mpmath, both representations, and the true zero
```
