# Claims and evidence — Conjecture 1.1 of Bétermin–Šamaj–Travěnec is false

Paths are relative to the repository root.

| # | Claim (precise) | Rigor | Digits | Novelty | Certificate | Lean statement | Witness | Notes |
| --- | --------------- | ----- | ------ | ------- | ----------- | -------------- | ------- | ----- |
| 1 | With Z(s, Δ) = (Δ/π)^s Γ(s) ζ⁽²⁾(s, Δ) and Δ* = e^γ/(4π): Z(1/2, Δ*) ∈ [1.1145061749791332998729770331571…·10⁻¹⁹ ± 2.5·10⁻⁶⁰], computed from the defining theta integral; it is positive, so Δ* is not a zero of ζ⁽²⁾(1/2, ·) and Conjecture 1.1 of arXiv:2110.09368 is false | numeric-experiment | 40 | no paper addressing the conjecture found | certificates/04-epstein-conjecture/epstein-bst.json |  |  | `epstein_arb.py` (Arb, 320 bits, rigorous quadrature, explicit tail bound). The Bessel-series ball overlaps. |
| 2 | Z(1/2, Δ* + 10⁻²⁰) ∈ [−7.5959239306301078709…·10⁻²⁰ ± 1.6·10⁻⁶⁰] < 0; hence a zero lies in (Δ*, Δ* + 10⁻²⁰), agreeing with e^γ/(4π) to twenty decimal places | numeric-experiment | 40 |  | certificates/04-epstein-conjecture/epstein-bst.json |  |  | Same script; root Δ\_c from `epstein_check.py`. |
| 3 | ζ⁽²⁾(1/2, Δ) = Δ⁻¹[γ − log(4πΔ) + 4 Σ\_{N≥1} d(N) K₀(2πN/Δ)], and γ − log(4πΔ*) = 0 exactly | conjectural |  |  |  |  |  | Poisson-summation derivation (main.md §2); cross-checked against the definition at four values of Δ (about 70 digits at three of them, about 40 at Δ = 0.9). Not needed for #1. |

## Reasoning

### #1

There are two independent legs.

- **Leg one, the identity (★).** At Δ* the first two terms cancel exactly, leaving a positive sum of K₀ terms.
- **Leg two, independent of (★).** The defining theta integral is enclosed by Arb at 320 bits: rigorous quadrature on [1, 600] plus an explicit tail bound. The resulting ball has a positive lower end and overlaps the Bessel-series ball.

What would change the conclusion: an error in the definition of Z, which is copied from the original paper's Eq. (2.1), or in the theta-integral representation, which is checked against (★) at four values of Δ.

### #2

At Δ* + 10⁻²⁰ the linear term of the small-Δ expansion contributes about −1.87·10⁻¹⁹, which outweighs the positive 1.1·10⁻¹⁹. Both representations give the same negative value. By continuity a zero lies between Δ* and Δ* + 10⁻²⁰, and by the original paper's uniqueness lemma it is the zero.
