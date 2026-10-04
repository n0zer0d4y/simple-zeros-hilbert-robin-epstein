---
title: "The odd analogue of Robin's 5040: a sharp threshold for the odd Robin criterion"
authors: ["Nozero Day"]
note: "Produced autonomously by AI agents running inside a custom research harness; see the repository README. Unrefereed."
status: draft
date: "2026-10-04"
---

# The odd analogue of Robin's 5040: a sharp threshold for the odd Robin criterion

## Summary

**Background.** Robin proved that the Riemann hypothesis (RH) is equivalent to σ(n) < e^γ n log log n for all n > 5040. Washington and Yang (arXiv:2008.04787, Theorem 1.2) proved the odd analogue: RH is equivalent to

  σ(n) < (e^γ/2) n log log n  for all odd n ≥ c₀ = 3⁴·5³·7²·11·13⋯67 = 18565284664427130919514350125.

Their proof identifies N = c₀/67 = 3⁴·5³·7²·11⋯61 = 277093800961598968947975375 as the last odd colossally abundant violator. They write: "We do not know whether the inequality is satisfied for N < n < c₀. In contrast to the situation in [13], the numbers here are large enough to make brute-force computation infeasible."

**Result.** We settle the gap by an exhaustive, pruned search over odd factorisations. **No odd n with N < n < c₀ violates the inequality.** Since N itself violates it, the threshold is sharp:

  **RH ⟺ σ(n) < (e^γ/2) n log log n for all odd n > N,** and N + 1 cannot be lowered.

This is the odd analogue of Robin's 5040. The closest approach in the gap is at n = 3N, with margin −0.0013894. A scan finds no violator in (N, 10⁶⁰]. Exactly 884 odd integers n ≥ 3 below 10¹²⁰ violate the inequality, and the largest is N.

## 1. Statement

For odd n ≥ 3 put V(n) = σ(n)/n − (e^γ/2) log log n; n is a *violator* if V(n) ≥ 0.

**Theorem.**
- (a) V(N) = +0.0044431252017577491913… > 0, so N is a violator.
- (b) V(n) < 0 for every odd n with N < n < c₀. The closest approach is V(3N) = −0.0013894019681237789271…, and V(c₀) = −0.00034342801313684807911….
- (c) Hence, with Washington–Yang's Theorem 1.2, RH ⟺ V(n) < 0 for all odd n > N, and N + 1 cannot be lowered.
- (d) No odd n in (N, 10⁶⁰] is a violator. Exactly 884 odd n ≥ 3 below 10¹²⁰ are violators, and the largest is N.

## 2. Method

Every violator n ≥ L := N + 1 satisfies σ(n)/n ≥ f(n) ≥ f(L), where f(L) = (e^γ/2) log log L = 3.65922201459838…, because f is increasing. So it suffices to enumerate all odd n ∈ [L, c₀ − 1] with σ(n)/n ≥ f(L), and then decide each one.

**Method A** (`odd_robin_gap.py`, python-flint). This is a depth-first search over odd factorisations n = Π q^e, with primes taken in increasing order and gaps allowed. It is pruned by a Lagrangian bound: for any λ ≥ 0 and any completion m ≤ B using only primes ≥ q\_j,

  ln(σ(m)/m) ≤ λ ln B + Σ\_{q ≥ q\_j} max\_{e ≥ 0} [ln(σ(q^e)/q^e) − λ e ln q].

The proof is one line: add and subtract λ e ln q, and use Σ e ln q ≤ ln B. With λ ≥ 10⁻⁵ only primes below about 1.1·10⁴ contribute.

**Method B** (`odd_robin_check_B.py`, mpmath). It uses a different bound and a different traversal. A completion has at most m distinct primes, the i-th smallest at least q\_{j+i}, and each contributes at most q/(q − 1) to σ(n)/n. Decisions use mpmath interval arithmetic with exact fractions.

Both methods return the same 1098 candidates (SHA-256 prefix of the sorted list: 4bf6339dd6b9b139), and none is a violator. The decisive margins at N, 3N and c₀ are recomputed from the exact rational σ(n)/n in `margins.py`. mpmath at 120 digits and python-flint balls at 400 bits agree in every printed digit.

**Sanity check.** The family search `coprime_robin.py`, run on all integers (k = 0), reproduces the 26 known Robin exceptions with n ≥ 3, the largest being 5040.

## 3. What is formal

`lean/SimpleZerosHilbertRobinEpstein/OddRobin/OddRobinCore.lean` proves two statements:
- **`violator_ratio_ge`:** the monotone reduction that defines the candidate set. A violator n ≥ L ≥ 3 has σ(n)/n ≥ (e^γ/2) log log L.
- **`sigma_div_le_prod`:** the pruning inequality of method B, σ(n)/n ≤ Π\_{p∣n} p/(p − 1).

Witness theorems show their hypotheses are satisfiable; for example, 3 is an odd violator. The completeness of the enumeration and the numerical margins are not formalised.

## 4. A contrast: coprimality to 6

For n coprime to the first k primes, the analogue is σ(n) < e^γ Π\_{i≤k}(1 − 1/p\_i) n log log n. For k = 2 (n coprime to 6), the same search finds 452 604 violators below 10¹²⁰, and the largest lies in the top decade [10¹¹⁹, 10¹²⁰), so the violations continue beyond the scanned range.

A heuristic from the Mertens product explains this. Coprimality to the first k primes shifts log log n by an amount of order (log log n)/log n, which exceeds the RH-level slack of order 1/√(log n) until log n is very large. For k = 1 the crossing happens near log n ≈ 61, which is N. So the odd threshold is a feature of k = 1; for k = 2 no threshold is visible below 10¹²⁰. This heuristic is not proved.

## 5. Honest scope

- This is a computer-assisted theorem. The enumeration is exhaustive, with completeness resting on a proved pruning inequality and two independent implementations, but it is not formally verified.
- It sharpens a theorem whose equivalence with RH is due to Washington and Yang, and it says nothing about the truth of RH.
- Literature searches (October 2026) found no resolution of the gap. A related but different odd analogue ("of the second type") is studied by Oshiro and Koya (2022).

## References

- G. Robin, *Grandes valeurs de la fonction somme des diviseurs et hypothèse de Riemann* (1984), zbMATH 3815763.
- L. C. Washington, A. Yang, *Analogues of the Robin–Lagarias criteria for the Riemann hypothesis*, arXiv:2008.04787, doi:10.1142/S1793042121500111 (Theorem 1.2, proof of Proposition 3.5).
- T. Oshiro, Y. Koya, *An analogue of the Robin inequality of the second type for odd integers* (2022).
