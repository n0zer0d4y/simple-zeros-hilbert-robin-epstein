# simple-zeros-hilbert-robin-epstein

Four small results in analytic number theory and special functions. Each comes with a written argument, rigorous interval-arithmetic or error-bounded certificates, and reproduction code. The finite cores of results 1 and 3 are formalised in a small Lean 4 library.

> **Status: unrefereed.** These results were produced autonomously by AI agents running inside a custom research harness; a human set the goals and decided what to publish. No human expert has reviewed them yet; such review is very welcome. None of them bears on the truth of the Riemann hypothesis.

## The four results

### 1. A whole-cell refinement of Wang's bound for simple zeros on the critical line

[`papers/01-simple-zeros-critical-line/`](papers/01-simple-zeros-critical-line/main.md)

- **The question.** Alpöge–Furman (arXiv:2608.13637) and Lamzouri (arXiv:2609.02882) proved that at least C₀ = 0.67250070… of the zeros of ζ are simple and on the critical line. Wang (arXiv:2609.24167) improved this by 6.67·10⁻⁸, by bounding a spectral term with triples of zeros.
- **The refinement.** Blocks of up to seven zeros, certified lower bounds for the minima of the kernel energies (ball arithmetic), and a line envelope anchored by a certified convex minorant. Given Wang's published inputs, this yields **liminf N₀ˢ(T)/N(T) ≥ 0.672724** and **liminf N\_d(T)/N(T) ≥ 0.836362**, a gain of 2.24·10⁻⁴.
- **Rigor.** Interval-arithmetic certificates for the minima. The block bound, the envelope, the deduction, the numeric instances and the Jensen anchor are proved in Lean.
- **Not a record.** Several unreviewed 2026 preprints claim larger values (up to about 0.6735) by related methods. This is an independent, fully reproducible and formalised data point; see the paper's "Not a record" table.

### 2. An explicit lower bound for the Montgomery–Vaughan constant

[`papers/02-montgomery-vaughan-constant/`](papers/02-montgomery-vaughan-constant/main.md)

- **The question.** The optimal constant C in the Montgomery–Vaughan weighted Hilbert inequality is unknown (Montgomery's Problem 21). Rodgers (arXiv:2608.12315) proved C > π + 1.68·10⁻⁸.
- **The result.** An explicit configuration of 60001 integer points with Gaussian-integer weights has ratio at least 3.1427910. Hence **C > 3.14279 = π + 1.19·10⁻³**.
- **Rigor.** An exact finite computation, checked by quad precision with an error bound, by ball arithmetic over all 3.6·10⁹ pairs, and by a third independent implementation.

### 3. The odd analogue of Robin's 5040

[`papers/03-odd-robin-threshold/`](papers/03-odd-robin-threshold/main.md)

- **The question.** Washington–Yang (arXiv:2008.04787) proved RH ⟺ σ(n) < (e^γ/2) n log log n for all odd n ≥ c₀ ≈ 1.86·10²⁸. They wrote that they did not know whether the inequality holds between N = c₀/67 and c₀, and that brute force is infeasible there.
- **The answer.** It does. **RH ⟺ σ(n) < (e^γ/2) n log log n for all odd n > N = 277093800961598968947975375**, and N + 1 is sharp.
- **Rigor.** Two independent exhaustive enumerations, with interval arithmetic for every decision. The reduction to the candidate set and the pruning inequality are proved in Lean.

### 4. A conjecture on the rectangular Epstein zeta function that is true to twenty digits and false

[`papers/04-epstein-conjecture/`](papers/04-epstein-conjecture/main.md)

- **The question.** Bétermin–Šamaj–Travěnec (arXiv:2110.09368, Conjecture 1.1) conjectured that the zero of Δ ↦ ζ⁽²⁾(1/2, Δ) is exactly e^γ/(4π).
- **The answer.** False. The function is positive there (+1.1145·10⁻¹⁹ after normalisation) and negative at e^γ/(4π) + 10⁻²⁰. The zero agrees with the conjectured value to twenty decimal places.
- **Rigor.** An exact Bessel-series formula, and an Arb enclosure computed directly from the defining theta integral.

## How these results were produced

The research was carried out autonomously by AI agents running inside a custom research harness. The computations and proofs use standard tools (python-flint, mpmath, a C compiler with quad precision, Lean 4 with Mathlib). What the system adds is discipline about evidence:

- **Every number is tied to a logged computation.** Before a result is reported, its numbers, confidence and citations are checked against a log of the computations and literature lookups that produced them, and anything unsupported is removed.
- **Every claim carries a rigor grade** (see [`docs/verification.md`](docs/verification.md)): proved in Lean, certified by interval or error-bounded arithmetic, cited, or conjectural.
- **Key results are cross-checked by independent implementations.** Two agents worked on the problems, and each recomputed the other's key results with its own code before they were kept.
- **Work persists across sessions** through a research memory that links each fact to the evidence behind it.

A human set the research goals and decided what to publish; the system chose the specific problems and carried out the work.

## Repository layout

```
papers/          one folder per result: main.md (the paper), claims.md (each claim, its evidence and rigor grade)
certificates/    certificate files (JSON) and, for result 2, the data files
code/            the scripts that produce the certificates, with the outputs of our runs
lean/            Lake package SimpleZerosHilbertRobinEpstein (Lean 4 + Mathlib)
docs/            reproducing.md, verification.md
```

## Reproducing

[`docs/reproducing.md`](docs/reproducing.md) lists the exact command for every certificate. In brief:

```
pip install -r requirements.txt
cd code/01-simple-zeros-critical-line && python bnb.py m3 4 0.000221935 200 && python final_constants.py
cd ../03-odd-robin-threshold && python odd_robin_check_B.py && python margins.py
cd ../04-epstein-conjecture && python epstein_arb.py
```

For the Lean library:

```
cd lean && lake exe cache get && lake build && lake env lean AxiomCheck.lean
```

## How much to trust each claim

Every claim carries a rigor grade in its paper's `claims.md`; see [`docs/verification.md`](docs/verification.md).

- **proved:** a Lean theorem, kernel-checked, depending only on `propext`, `Classical.choice` and `Quot.sound`.
- **numeric-experiment:** rigorous interval (Arb) or error-bounded arithmetic, reproducible from `code/`.
- **reference:** a published or preprinted result.
- **conjectural:** a written argument that is not formalised, or a conclusion resting on an unrefereed preprint. The headline of result 1 is in this class because Wang's preprint is unrefereed. So is the completeness argument behind result 3.

## Prior art

- **Result 1:** Alpöge–Furman, Lamzouri and Wang, read. Unreviewed 2026 preprints by Singh, Schäfer, Gebendorfer, Komada, Devine, Santibáñez-Leal and others claim related or larger bounds; we read only their abstracts.
- **Result 2:** Montgomery–Vaughan 1974, Preissmann 1984 and Rodgers 2026, read. Rodgers mentions an unpublished numerical certificate for N = 10000 whose value we do not know.
- **Result 3:** Washington–Yang, read. No resolution of their question was found. A different odd analogue ("of the second type") is studied by Oshiro–Koya (2022).
- **Result 4:** Bétermin–Šamaj–Travěnec (arXiv version), read. No paper addressing Conjecture 1.1 was found.

Literature searches were made in October 2026. Absence from them is evidence of novelty, not proof of it.

## License

Code (`code/`, `lean/`): MIT, see [`LICENSE`](LICENSE). Papers and documentation: CC BY 4.0, see [`LICENSE-docs`](LICENSE-docs).

## Citation

See [`CITATION.cff`](CITATION.cff).
