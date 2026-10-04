# Verification

## Rigor grades

Each paper folder has a `claims.md` with one row per claim: the exact statement, its rigor grade, the certificate or Lean file it rests on, and notes. Under `## Reasoning` it gives the argument for each row.

| Grade              | Meaning                                                                                                             | How to check it                                                                    |
| ------------------ | ------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------- |
| proved             | a Lean 4 theorem, kernel-checked, depending only on the standard axioms `propext`, `Classical.choice`, `Quot.sound` | `cd lean && lake build && lake env lean AxiomCheck.lean`                           |
| numeric-experiment | rigorous interval (Arb ball) or error-bounded arithmetic, run locally and reproducible from `code/`                 | re-run the command in `reproducing.md`; the output must match the certificate file |
| reference          | a published or preprinted result                                                                                    | the cited paper                                                                    |
| conjectural        | a written argument that is not formalised, or a conclusion that rests on an unrefereed preprint                     | read the argument; independent review is welcome                                   |

**A note on "numeric-experiment".** These computations carry guaranteed error radii (Arb balls) or a priori rounding-error bounds (the quad-precision program). They were run locally and are not formally verified. Where two independent implementations exist, the claims table says so.

## What the certificates prove

- **Branch and bound** (result 1). The domain of gap vectors is covered by cells. On each cell a rigorous Taylor lower bound is evaluated in ball arithmetic: the value at the centre, minus the gradient term, minus a second-order term from a proved bound on (K₀²)″. A cell is dropped once its lower bound reaches the target. A run is certified when no cell remains, so the target is a lower bound for the minimum. Negative controls (targets above the best values found) must fail, and do.
- **Exact finite ratios** (result 2). For integer data the ratio is a rational number. Two programs with different arithmetic (quad precision with an error bound, and ball arithmetic) agree to 27 digits, and a third agrees to 16.
- **Exhaustive enumeration** (result 3). Completeness rests on a proved pruning inequality. Two implementations with unrelated bounds return the same 1098 candidates, and each is decided in interval arithmetic. The reduction to the candidate set and the elementary pruning inequality are proved in Lean.
- **Interval enclosure from a definition** (result 4). Arb's rigorous quadrature of the defining theta integral, plus an explicit tail bound.

## Inputs taken from the literature

Result 1 assumes Proposition 2.1, the block argument of Lemma 3.1 and the asymptotics of Section 4 of Wang's preprint arXiv:2609.24167, together with Lamzouri's asymptotics. These enter the Lean statements as explicit hypotheses and are not re-derived. Result 3's equivalence with the Riemann hypothesis is Theorem 1.2 of Washington–Yang (arXiv:2008.04787).

## Review

- **Internal review.** Each argument was reviewed adversarially by a second, independent agent of the research system. That agent also recomputed the certificates for result 1 (cell length 4) and result 2 with its own code.
- **Human review.** No human expert has refereed these results yet.
