---
title: "An explicit configuration with ratio 3.14279 in the Montgomery–Vaughan weighted Hilbert inequality"
authors: ["Nozero Day"]
note: "Produced autonomously by AI agents running inside a custom research harness; see the repository README. Unrefereed."
status: draft
date: "2026-10-04"
---

# An explicit configuration with ratio 3.14279 in the Montgomery–Vaughan weighted Hilbert inequality

## Summary

**Background.** Montgomery and Vaughan proved that for distinct reals λ\_1, …, λ\_N, complex w\_m and δ\_m = min\_{n≠m} |λ\_m − λ\_n|,

|Σ\_{m≠n} w\_m conj(w\_n)/(λ\_m − λ\_n)| ≤ C Σ\_m |w\_m|²/δ\_m (1)

holds with C = 3π/2. They asked whether C = π is admissible (Problem 21 of Montgomery's \_Ten Lectures\_). The best upper bound is C ≤ π√(1 + (2/3)√(6/5)) ≈ 4.1325 (Preissmann). Rodgers (arXiv:2608.12315, August 2026) proved C > π, through an eigenvalue π + 1.68·10⁻⁸ of a limiting operator. He conjectured from numerics that the optimal constant is about 3.143.

**Result.** We give explicit data: N = 60001 integer positions λ\_m and Gaussian-integer weights w\_m. For these, the ratio of the two sides of (1) is, by an exact finite computation, at least 3.1427910. Hence

**C > 3.14279 = π + 1.19·10⁻³.**

The excess over π is about 70 000 times that of the best lower bound we found in print, Rodgers' π + 1.68·10⁻⁸. Rodgers mentions (Remark 2.3) an unpublished numerical certificate for N = 10000 whose value we do not know.

## 1. Why one configuration is a proof

If (1) holds for all admissible data with a constant C, then C is at least the ratio R(λ, w) = |Σ\_{m≠n} w\_m conj(w\_n)/(λ\_m − λ\_n)| / Σ\_m |w\_m|²/δ\_m for every single choice of data.

Write w = a + ib. The kernel is antisymmetric, so the double sum equals 2iT with T = Σ\_{m≠n} b\_m a\_n/(λ\_m − λ\_n), and R = 2|T| / Σ(a\_m² + b\_m²)/δ\_m. For integer positions and integer a, b, R is an explicit rational number: there are no square roots and no analytic input.

## 2. The data and their verification

| N     | extent λ\_N − λ\_1 | ratio R (lower bound) | R − π                   |
| ----- | ---------------- | --------------------- | ----------------------- |
| 3201  | 1.5·10⁶          | 3.1398089             | −1.78·10⁻³ (validation) |
| 12801 | 2.4·10⁷          | 3.1420123             | +4.20·10⁻⁴              |
| 20001 | 5.9·10⁷          | 3.1423304             | +7.38·10⁻⁴              |
| 30001 | 5.0·10⁸          | 3.1425565             | +9.64·10⁻⁴              |
| 40001 | 8.9·10⁸          | 3.1426672             | +1.07·10⁻³              |
| 60001 | 2.0·10⁹          | **3.1427910**         | **+1.20·10⁻³**          |

The data files are in [`certificates/02-montgomery-vaughan-constant/data/`](../../certificates/02-montgomery-vaughan-constant/data/), with SHA-256 hashes in `mv-constant.json`. Each ratio was computed by independent programs:

- **Quad precision with an error bound** (`mvcert.c`, `gcc -O2 mvcert.c -lquadmath`). The terms a\_n/(λ\_m − λ\_n) are computed in `__float128` (113-bit significand), with the a-priori bound (2N + 4)·2⁻¹¹³·Σ|terms| on the accumulated rounding error. The relative error bound is below 10⁻²⁸ at every size.
- **Ball arithmetic over all pairs** (`verify_mv_txt.py ... B`, python-flint): every pair term is summed as an Arb ball. At N = 60001 this is 3.6·10⁹ pairs in 1174 s.
- **Exact integer correlation** (`verify_mv_txt.py ... A`, for extents up to a few 10⁷): T = Σ\_{d≥1} (c\_d − c\_{−d})/d, with c\_d = Σ\_{λ\_m − λ\_n = d} b\_m a\_n computed by an exact integer polynomial product.
- **A separate binary64 implementation** with an a-priori summation bound and comparisons in exact fractions. It agreed with the values above to 16 digits at N = 12801, 20001, 30001, 40001 and 60001.

The quad-precision and ball-arithmetic results agree to 27 digits at every size where both were run.

## 3. The configurations

Rodgers' public repository conjectures symmetric extremal gap lists: a central block of gap 1 flanked by lattices of growing gap. Our data have this shape with integer gaps. At N = 60001:

- a central block of gap 1 with 42 913 points (about 0.72 N);
- on each side, four lattices with gaps 2700, 48331, 459143 and 4361855 (γ\_1 = 0.045 N, then ratios about 17.9, 9.5 and 9.5) and 6600, 1314, 468 and 162 points (about 0.11 N, 0.0219 N, 0.0078 N and 0.0027 N).

The weights are the top singular vector of the matrix B\_mn = √(δ\_m δ\_n)/(λ\_m − λ\_n). It is computed in the half-size real matrix M\_ik = B\_ik + B\_ik′ (the reflection maps B to −B), then rounded to 44-bit integers; rounding costs about 10⁻¹⁴ in the ratio. `e14_big.py` regenerates the data, and needs a few GB of memory at the largest size.

The landscape is very flat: in a search at N = 3201, scaling a level-gap ratio by a factor in [1/2, 2] changed the ratio by less than 10⁻⁴. The gains shrink as N grows (table above); we make no claim about the limiting value.

## 4. Honest scope

- The true constant C is not determined. The lower bound 3.1427910 is below Rodgers' conjectured 3.143, and the upper bound 4.1325 is unchanged.
- The configurations are not shown to be extremal.
- Only the finite computations are claimed; each can be checked from the data files.
- Literature searches (October 2026) found no lower bound above Rodgers' printed value. His unpublished N = 10000 certificate may be larger than his printed value.

## References

- H. L. Montgomery, R. C. Vaughan, \_Hilbert's inequality\_, J. London Math. Soc. (2) 8 (1974), doi:10.1112/jlms/s2-8.1.73.
- H. L. Montgomery, \_Ten lectures on the interface between analytic number theory and harmonic analysis\_, CBMS 84 (1994), Problem 21.
- E. Preissmann, \_Sur une inégalité de Montgomery–Vaughan\_ (1984), zbMATH 3873435.
- B. Rodgers, \_On the optimal constant in the Montgomery–Vaughan weighted Hilbert inequality\_, arXiv:2608.12315 (2026); repository github.com/brad-rodgers/extremalconfigs.
- W. Yangjit, \_On the Montgomery–Vaughan weighted generalization of Hilbert's inequality\_, arXiv:2203.14950, doi:10.1090/bproc/199.
