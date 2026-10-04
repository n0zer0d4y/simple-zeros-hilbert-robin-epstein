---
title: "A conjecture on the real zero of the rectangular Epstein zeta function that is true to twenty digits and false"
authors: ["Nozero Day"]
note: "Produced autonomously by AI agents running inside a custom research harness; see the repository README. Unrefereed."
status: draft
date: "2026-10-04"
---

# A conjecture on the real zero of the rectangular Epstein zeta function that is true to twenty digits and false

## Summary

Bétermin, Šamaj and Travěnec (arXiv:2110.09368, Conjecture 1.1) consider the Epstein zeta function of the rectangular lattice ℤ ⊕ Δℤ,

  ζ⁽²⁾(s, Δ) = ½ Σ′ (j² + Δ²k²)^{−s}.

They conjecture that the unique zero of Δ ↦ ζ⁽²⁾(1/2, Δ) on (0, 1) is Δ* = e^γ/(4π), reporting agreement with the numerical zero "by at least 22 decimal digits".

**Result. The conjecture is false.** An exact Bessel-series formula gives

  ζ⁽²⁾(1/2, Δ) = Δ⁻¹ [γ − log(4πΔ) + 4 Σ\_{N≥1} d(N) K₀(2πN/Δ)].  (★)

At Δ = Δ* the first two terms cancel exactly, and every K₀ term is positive, so ζ⁽²⁾(1/2, Δ*) > 0.

This is also verified directly from the defining theta integral with rigorous interval arithmetic, without using (★): √Δ* · ζ⁽²⁾(1/2, Δ*) = +1.1145·10⁻¹⁹. The same function is negative at Δ* + 10⁻²⁰. So the zero lies in (Δ*, Δ* + 10⁻²⁰). It agrees with e^γ/(4π) to twenty decimal places and differs in the twenty-first: Δ\_c − Δ* = 5.947·10⁻²¹.

## 1. Statement

**Theorem.** Let Z(s, Δ) = (Δ/π)^s Γ(s) ζ⁽²⁾(s, Δ), so that Z(1/2, Δ) = √Δ ζ⁽²⁾(1/2, Δ), and put Δ* = e^γ/(4π) = 0.14173323966388719138946879310…. Then

  Z(1/2, Δ*) = 4 Δ*^{−1/2} Σ\_{N≥1} d(N) K₀(2πN/Δ*) > 0,

numerically Z(1/2, Δ*) = 1.1145061749791332998…·10⁻¹⁹, and Z(1/2, Δ* + 10⁻²⁰) = −7.5959239306301078709…·10⁻²⁰ < 0. Hence Δ* is not a zero of ζ⁽²⁾(1/2, ·), Conjecture 1.1 is false, and a zero lies in (Δ*, Δ* + 10⁻²⁰). The zero is Δ\_c = 0.141733239663887191395415685084185023623….

## 2. The exact formula

Write ζ⁽²⁾(s, Δ) = Δ^{−2s} ζ(2s) + Σ\_{j≥1} Σ\_{k∈ℤ} (j² + Δ²k²)^{−s}; the first term collects j = 0. Poisson summation in k gives, for a, b > 0,

  Σ\_k (a² + b²k²)^{−s} = √π Γ(s − ½) a^{1−2s} / (Γ(s) b) + (4√π / (Γ(s) b)) Σ\_{m≥1} (πm/(ab))^{s−½} K\_{s−½}(2πam/b).

Take a = j and b = Δ, sum over j, and let s = ½ + ε. The terms Δ^{−1−2ε} ζ(1 + 2ε) and √π Γ(ε) ζ(2ε)/(Δ Γ(½ + ε)) each have a simple pole at ε = 0, and the poles cancel. Their finite parts combine to (γ − log(4πΔ))/Δ, using ζ(0) = −½, ζ′(0) = −½ log 2π and ψ(½) = −γ − 2 log 2. At s = ½ the Bessel factor is K₀, which gives (★). At Δ = Δ* the bracket's first two terms vanish exactly, and the sum is positive. ∎

## 3. Verification

- **Two representations agree.** The defining integral Z(1/2, Δ) = −2 + ∫₁^∞ t^{−1/2} [θ₃(e^{−πtΔ}) θ₃(e^{−πt/Δ}) − 1] dt (Riemann's method applied to the definition) and the Bessel series (★) agree to about 70 digits at Δ = Δ*, 0.3 and 0.14, and to about 40 digits at Δ = 0.9 (`epstein_check.py`, mpmath).
- **Rigorous enclosure from the definition** (`epstein_arb.py`, Arb balls at 320 bits). The integral over [1, 600] uses Arb's rigorous quadrature, and the tail is bounded by 4.1·T^{−1/2} e^{−πΔT}/(πΔ). This encloses Z(1/2, Δ*) in [1.1145061749791332998729770331571…·10⁻¹⁹ ± 2.5·10⁻⁶⁰], which is positive, and Z(1/2, Δ* + 10⁻²⁰) in a negative ball. The Bessel-series ball at Δ* overlaps the first ball.
- **The true zero.** A root-finder on (★) gives Δ\_c − Δ* = 5.947·10⁻²¹ (relative 4.2·10⁻²⁰).

## 4. Why the numerical evidence misled

The two-term small-Δ expansion is exact up to terms of size e^{−2π/Δ}. At Δ* this is e^{−2π/Δ*} ≈ e^{−44.3} ≈ 6·10⁻²⁰, the same order as the residual 1.1·10⁻¹⁹ at e^γ/(4π). A conjectured closed form for a zero of such a function will always agree with numerics to the size of the exponentially small remainder. The correct statement is Δ\_c = Δ* + O(e^{−2π/Δ*}).

## 5. Honest scope

- The identity (★) is a standard Poisson-summation computation, cross-checked numerically and not formalised. The refutation does not depend on it: the definition-based Arb enclosure verifies the sign on its own.
- Literature searches (October 2026) found no paper addressing Conjecture 1.1. The journal version of the original paper was not read.
- This concerns a lattice-sum zero; it says nothing about the Riemann zeta function.

## References

- L. Bétermin, L. Šamaj, I. Travěnec, *Interplay between critical and off-critical zeros of two-dimensional Epstein zeta functions*, arXiv:2110.09368 (2021) (Conjecture 1.1, Section 4.2; Theorems 2.1 and 3.7; Lemma 4.4).
