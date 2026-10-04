---
title: "A whole-cell refinement of Wang's bound for the proportion of simple zeros of ζ on the critical line"
authors: ["Nozero Day"]
note: "Produced autonomously by AI agents running inside a custom research harness; see the repository README. Unrefereed."
status: draft
date: "2026-10-04"
---

# A whole-cell refinement of Wang's bound for the proportion of simple zeros of ζ on the critical line

## Summary

**Background.** Alpöge and Furman (arXiv:2608.13637, August 2026) proved unconditionally that at least

C₀ = 3/2 − cot(1/√2)/√2 = 0.67250070367941164…

of the nontrivial zeros of ζ are simple and on the critical line (with the Montgomery–Taylor window), and at least (1 + C₀)/2 = 0.83625… are distinct. Lamzouri gave a second proof. Wang (arXiv:2609.24167, September 2026) improved the first constant by δ₀ = 6.67·10⁻⁸ and the second by δ₀/2. He kept a spectral term Δ\_K = tr Ψ(G\_K) in Lamzouri's inequality and bounded it with disjoint triples of zeros in cells of length H, using an analytic three-point bound.

**What is done here.** We keep Wang's Proposition 2.1, his block argument (Lemma 3.1) and his asymptotics (Section 4) as published inputs. We change only the counting:

1. blocks of any size up to seven points, instead of triples;
2. the true minima of the k-point energies Σ\_{i<j} K₀(x\_i − x\_j)², certified by interval arithmetic, instead of the analytic three-point bound (which is about 400 times smaller at H = 4);
3. a line Ψ\_k ≥ s k − t for the minimal value Ψ\_k of tr Ψ over k points in a cell, extended to all k by superadditivity from an anchor given by a certified convex minorant of K₀².

**Result.** Given Wang's published inputs:

| cell length H | certified inputs               | simple and on the line | distinct       | gain over C₀  |
| ------------- | ------------------------------ | ---------------------- | -------------- | ------------- |
| 4             | 3- and 4-point minima          | ≥ 0.672577             | ≥ 0.836288     | 7.66·10⁻⁵     |
| 7             | 3- to 6-point minima, minorant | ≥ 0.672665             | ≥ 0.836332     | 1.64·10⁻⁴     |
| 8             | 3- to 7-point minima, minorant | **≥ 0.672724**         | **≥ 0.836362** | **2.24·10⁻⁴** |

The gain at H = 8 is about 3360 times Wang's δ₀. The finite part of the argument (block bound, envelope, deduction, numeric instances, Jensen anchor and minorant) is formalised in Lean 4 with Mathlib; the analytic inputs and the certified minima enter the Lean statements as hypotheses.

**Not a record.** Several unreviewed 2026 preprints claim larger proportions by related methods. We have read at most their abstracts:

| preprint                                                                    | claim                                      | method, per its abstract                                                                               |
| --------------------------------------------------------------------------- | ------------------------------------------ | ------------------------------------------------------------------------------------------------------ |
| K. Singh, "An Unconditional 67.345129% Lower Bound …"                       | 0.67345129                                 | not read beyond the title                                                                              |
| D. Schäfer, "A Certified Finite Refinement for Simple and Distinct Zeros …" | 0.67342504 (simple), 0.83671252 (distinct) | a seven-point pressure certificate; a six-dimensional gap inequality certified by interval subdivision |
| "tawanerguo-cn", "Certified unconditional 67.3192911473% lower bound …"     | 0.67319291                                 | not read beyond the title                                                                              |
| J. J. Gebendorfer, "An expanded window and joint position pressures …"      | not read                                   | —                                                                                                      |
| T. Komada, "A Lean-Verified Refinement … (67.251%)"                         | 0.67251263                                 | Lean-verified; local Gram interactions between consecutive zeros                                       |
| M. Devine, "A Computation-Free Spectral Improvement …"                      | some δ > 0                                 | qualitative, from the sum-free zero set of K₀                                                          |
| F. A. Santibáñez-Leal, "A sharp three-point kernel bound …"                 | 0.67250080                                 | the sharp form of Wang's three-point ratio                                                             |

Links are in the references. Our method, multi-point minima of the kernel energy certified by interval subdivision, is close to Schäfer's. What this repository offers is an independent, fully reproducible and formalised data point in the same framework, not a new record.

## 1. Setting

Let Z be the multiset of normalised zero ordinates of ζ up to height T, as in Wang's setting (N = N(T) elements). Let n = N₀ˢ(T) be the number of simple zeros on the line ("simple real elements") and D the number of distinct zeros. Let K = f̂ for a kernel f = η² supported in [−1/2, 1/2] with ∫f = 1. Wang's Proposition 2.1 reads

n ≥ 2N − E\_K + Δ\_K, D ≥ 3N/2 − E\_K/2 + Δ\_K/2,

with E\_K = Σ\_{z,s} K(z − s)² and Δ\_K = tr Ψ(G\_K). Here G\_K = [K(x\_i − x\_j)] is the Gram matrix of the simple real elements and Ψ(t) = (t − 1)² for t ≤ 2, 2t − 3 for t > 2.

For the Montgomery–Taylor kernel K₀ = f̂₀, with f₀(u) = cos(√2 u)/(√2 sin(1/√2)) on [−1/2, 1/2], one has E\_K = (2 − C₀ + o(1))N (Lamzouri's asymptotics as used in Wang's Section 4). Without Δ\_K this gives n/N ≥ C₀. Explicitly,

K₀(x) = c (sinc A + sinc B), c = 1/(2√2 sin(1/√2)), A = (√2 − 2πx)/2, B = (√2 + 2πx)/2,

and |K₀| ≤ 1, |K₀′| ≤ π, |K₀″| ≤ π² because f₀ is a probability density supported in [−1/2, 1/2].

## 2. The argument

(a) **Partition step.** For disjoint index sets, tr Ψ(G\_K) is at least the sum of tr Ψ over the principal blocks. Wang's proof of Lemma 3.1 (orthogonal coordinate subspaces, an orthonormal eigenbasis of each block, convexity of Ψ and Jensen) holds for blocks of any size.

(b) **Block bound.** A Gram block B with unit diagonal has tr Ψ(B) ≥ min(1, Σ\_{i≠j} B\_ij²) = min(1, 2 Σ\_{i<j} K(x\_i − x\_j)²). If every eigenvalue is at most 2, then tr Ψ(B) = Σ(λ\_i − 1)² = ‖B − I‖²\_F. If some eigenvalue exceeds 2, then tr Ψ(B) > 1.

(c) **Cells.** Split the real axis into cells of length H (M = (1 + o(1)) N/H of them). Let Ψ\_k be the minimum of tr Ψ over k points in an interval of length H, and P\_k(H) the minimum of the pair energy Σ\_{i<j} K₀(x\_i − x\_j)² over the same configurations. Then Ψ\_k ≥ min(1, 2P\_k), Ψ\_k is non-negative and superadditive (pinch a block into two), and Δ\_K ≥ Σ\_cells Ψ\_{k\_c}.

(d) **Line.** If Ψ\_k ≥ s k − t for every k, then Δ\_K ≥ s n − t M, and Wang's inequality gives

n/N ≥ u := (C₀ − t/H)/(1 − s) − o(1), D/N ≥ (1 + C₀)/2 + (s u − t/H)/2 − o(1).

A line holds for every k once it holds below an anchor K (base cases) and s K ≤ Ψ\_K: induction with superadditivity, Ψ(j + K) ≥ Ψ(j) + Ψ(K).

(e) **Anchor.** Let φ be a convex, non-increasing minorant of K₀² on [0, ∞). K points in an interval of length H = K − 1 have K − 1 adjacent gaps of mean at most 1. The pair energy is at least the adjacent-pair energy, which by Jensen is at least (K − 1) φ(1). So Ψ\_K ≥ min(1, 2(K − 1) φ(1)).

At H = 4 the line is Ψ\_k ≥ Ψ₃(k − 2), which holds once Ψ₄ ≥ 4Ψ₃. At H = 7 and 8 the line is fixed by the certified values at the two block sizes around the mean occupation C₀H (about 4.7 and 5.4): k = 4, 5 at H = 7 and k = 5, 6 at H = 8.

## 3. The certified minima

K₀² is small only when every pair distance sits near a zero of K₀ (near 1.06, 2.03, 3.02, 4.02, …). The minima sit at gap patterns near those zeros. For example, the four-point minimum at H = 4 is near the gaps (1.0408, 1.0330, 1.0408), and the six-point minimum at H = 7 is near (1.0408, 1.0372, 1.9773, 1.0372, 1.0408).

The lower bounds are certified by a feasibility branch and bound in python-flint ball arithmetic (128 bits). A cube cell of half-width r about c is dropped when E(c) − r|∇E(c)|₁ − (second-order term) is at least the target, and undropped cells are split. The second-order term uses a global constant from the derivative bounds of §1 at cell length 4, and at cell lengths 7 and 8 a rigorous enclosure of (K₀²)″ over the range of each window sum on the cell.

| quantity                                    | certified lower bound                                           | cells                             |
| ------------------------------------------- | --------------------------------------------------------------- | --------------------------------- |
| m(4) = P₃(4)                                | 0.000221935                                                     | 21 319                            |
| P₄(4)                                       | 0.002116538 (and 0.0009)                                        | 487 917                           |
| P₃(7), P₄(7), P₅(7), P₆(7)                  | 1.13307e-5, 1.43197e-4, 7.52866e-4, 3.0683e-3                   | 1 980; 26 895; 284 454; 3 288 002 |
| P₃(8), P₄(8), P₅(8), P₆(8)                  | 6.43552e-6, 7.05725e-5, 4.91377e-4, 1.5534e-3                   | 2 627; 42 864; 554 282; 6 225 428 |
| P₇(8)                                       | 3.75e-3 (about 77% of the best value found; all the line needs) | 69 435 168                        |
| φ ≤ K₀² on [0, 1.06], for the 40 lines of φ | smallest lower bound about 4e-9                                 | 3 086                             |

The targets at H = 7 and 8 are 0.97 times the best values found by a structured global search over gap patterns near the zeros of K₀. Random multi-start search alone missed three minima. Every certified number is a rigorous lower bound whatever the true minima are: a lower basin could only make a certificate fail, never make one wrong. As negative controls, targets slightly above the best values fail with cells left at the maximum level.

**The lines.**

- **H = 7:** s = 12194/10⁷, t = 45914/10⁷, anchor K = 8 with Ψ₈ ≥ 14 φ(1).
- **H = 8:** s = 21240/10⁷, t = 96373/10⁷, anchor K = 9 with Ψ₉ ≥ 16 φ(1).
- **Both:** φ(1) ≥ 141397/(5·10⁷).

`final_constants.py` checks every base case and anchor in exact rationals and evaluates the bounds in 256-bit balls.

## 4. What is formal

The Lean 4 library in [`lean/`](../../lean/) has three result-1 files (namespace `SimpleZerosHilbertRobinEpstein.SimpleZeros`):

- **`WangCellBound.lean`:**
  - the block bound for eigenvalues, and for real symmetric Gram blocks with unit diagonal (via the spectral theorem);
  - the H = 4 envelope Ψ\_k ≥ (k − 2)Ψ₃;
  - the cell sum, the deduction and its liminf form, and the numeric corollary at H = 4.
- **`WangCellLine.lean`:**
  - the line form by induction with superadditivity;
  - the liminf forms for simple and for distinct zeros;
  - the numeric instances `simple_numeric_H7`, `distinct_numeric_H7`, `simple_numeric_H8` and `distinct_numeric_H8`.
- **`WangCellAnchor.lean`:**
  - Jensen over adjacent gaps;
  - convexity and antitonicity of the concrete φ = max(0, 40 lines), with the lines equal as exact rationals to the certified ones;
  - φ(1) ≥ 141397/(5·10⁷), and the H = 8 anchor inequality.

The main statements (`simple_on_line_numeric`, the four numeric instances, `pair_sum_anchor_phi`) have witness theorems that instantiate all of their hypotheses, so they are not vacuous. Every theorem listed in `AxiomCheck.lean` depends only on `propext`, `Classical.choice` and `Quot.sound`, and the library contains no `sorry`.

**Not formalised:**

- Wang's Proposition 2.1, the partition inequality for G\_K, and the asymptotics of E\_K and of the cell count; these are hypotheses of the Lean statements;
- the Taylor constants and second-derivative enclosures, the certified minima, and the inequality φ ≤ K₀²; these are the interval-arithmetic certificates.

## 5. Honest scope

- The theorem rests on Wang's September 2026 preprint (Proposition 2.1, Lemma 3.1, Section 4), read but not re-derived and not refereed.
- The minima are certified by our own interval-arithmetic code. Two independent implementations (binary64 with an explicit rounding slack, and ball arithmetic) agree at H = 4.
- The cell method discards interactions between cells, which limits how far it can go. Larger H needs higher-dimensional certificates (P₇(8) is six-dimensional and took 23 minutes on one core).
- See the "Not a record" table above: larger values are claimed by unreviewed preprints.
- A proportion of simple zeros on the line says nothing about the remaining zeros and cannot prove the Riemann hypothesis.

## References

- L. Alpöge, R. Furman, \_More than two thirds of the zeta zeros are simple and on the critical line\_, arXiv:2608.13637 (2026).
- Y. Lamzouri, \_A new proof that more than 2/3 of the zeros of the Riemann zeta function are simple and on the critical line\_, arXiv:2609.02882 (2026).
- B. Wang, \_Proportions of the non-trivial zeros of the Riemann zeta function\_, arXiv:2609.24167 (2026): Theorem 1.1, Proposition 2.1, Lemma 3.1, Lemma 3.2, Section 4.
- Unreviewed 2026 preprints, abstracts only:
  - K. Singh, https://exa.ai/library/publication/hj9qp8hbny5
  - D. Schäfer, https://exa.ai/library/publication/1wg1nprx720 and https://exa.ai/library/publication/8k373f84c3k
  - "tawanerguo-cn", https://exa.ai/library/publication/7jj1gbfflgw
  - J. J. Gebendorfer, https://exa.ai/library/publication/c64rhqtgzhg
  - T. Komada, https://exa.ai/library/publication/f6ry3jyhjp1
  - M. Devine, https://exa.ai/library/publication/56d9vmclx37
  - F. A. Santibáñez-Leal, https://exa.ai/library/publication/nmlfyjfr9bp
