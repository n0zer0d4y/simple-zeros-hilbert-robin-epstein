import Mathlib

/-!
# The odd Robin inequality: the formal core (papers/03-odd-robin-threshold)

Washington-Yang: RH is equivalent to `σ n < (e^γ / 2) * n * log log n` for all odd `n ≥ c₀`.
The gap `N < n < c₀` is settled by a computer-assisted enumeration (papers/03-odd-robin-threshold).
This file formalises the load-bearing, enumeration-independent pieces:

* `Violator n`: the odd Robin violator predicate.
* `violator_ratio_ge`: the monotone reduction. A violator `n ≥ L` has `σ n / n ≥ (e^γ/2) log log L`,
  so the violators in a range are among the integers with abundancy at least the threshold at its start.
* `sigma_div_le_prod`: the elementary pruning inequality `σ n / n ≤ ∏_{p ∣ n} p / (p - 1)`
  (method B of the enumeration uses exactly this bound).

What is NOT formalised here: the completeness of the enumeration (a verified branch-and-bound) and the
numerical margins (they need sharp rational bounds for `γ` and `log log n`, which Mathlib only has in crude form).
-/

namespace SimpleZerosHilbertRobinEpstein.OddRobin

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

/-- `n` is an odd violator of the odd Robin inequality `σ n < (e^γ / 2) * n * log log n`. -/
def Violator (n : ℕ) : Prop :=
  Odd n ∧ 3 ≤ n ∧
    Real.exp Real.eulerMascheroniConstant / 2 * n * Real.log (Real.log n) ≤ ((σ 1 n : ℕ) : ℝ)

/-- `log 3 > 1`, used to keep `log log` monotone on `n ≥ 3`. -/
lemma one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  rw [← Real.exp_lt_exp, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  have := Real.exp_one_lt_d9
  norm_num at this ⊢
  linarith

/-- The monotone reduction: a violator `n ≥ L` (with `3 ≤ L`) has abundancy at least the threshold at `L`. -/
theorem violator_ratio_ge {L n : ℕ} (hL : 3 ≤ L) (hLn : L ≤ n) (hv : Violator n) :
    Real.exp Real.eulerMascheroniConstant / 2 * Real.log (Real.log L) ≤ ((σ 1 n : ℕ) : ℝ) / n := by
  obtain ⟨_, _, h⟩ := hv
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hlogL : 1 < Real.log (L : ℝ) :=
    lt_of_lt_of_le one_lt_log_three (Real.log_le_log (by norm_num) hL3)
  have hmono : Real.log (Real.log L) ≤ Real.log (Real.log n) :=
    Real.log_le_log (by linarith) (Real.log_le_log hLpos (by exact_mod_cast hLn))
  rw [le_div_iff₀ hnpos]
  have hE : 0 < Real.exp Real.eulerMascheroniConstant / 2 := by positivity
  calc Real.exp Real.eulerMascheroniConstant / 2 * Real.log (Real.log L) * n
      ≤ Real.exp Real.eulerMascheroniConstant / 2 * Real.log (Real.log n) * n := by
        gcongr
    _ = Real.exp Real.eulerMascheroniConstant / 2 * n * Real.log (Real.log n) := by ring
    _ ≤ ((σ 1 n : ℕ) : ℝ) := h

/-- For a prime `p` and `e : ℕ`, `σ(p^e) (p - 1) < p^(e+1)`. -/
lemma sigma_prime_pow_mul_lt {p : ℕ} (hp : p.Prime) (e : ℕ) :
    ((σ 1 (p ^ e) : ℕ) : ℝ) * ((p : ℝ) - 1) < (p : ℝ) ^ (e + 1) := by
  rw [sigma_one_apply_prime_pow hp]
  push_cast
  rw [geom_sum_mul (p : ℝ) (e + 1)]
  linarith

/-- The elementary abundancy bound: `σ n / n ≤ ∏_{p ∣ n} p / (p - 1)` for `n ≠ 0`. -/
theorem sigma_div_le_prod {n : ℕ} (hn : n ≠ 0) :
    ((σ 1 n : ℕ) : ℝ) / n ≤ ∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
  have hmult : σ 1 n = n.factorization.prod (fun p k => σ 1 (p ^ k)) :=
    isMultiplicative_sigma.multiplicative_factorization _ hn
  have hnfac : n = n.factorization.prod (fun p k => p ^ k) :=
    (Nat.factorization_prod_pow_eq_self hn).symm
  rw [Nat.prod_factorization_eq_prod_primeFactors] at hmult hnfac
  have h1 : ((σ 1 n : ℕ) : ℝ) =
      ∏ p ∈ n.primeFactors, ((σ 1 (p ^ n.factorization p) : ℕ) : ℝ) := by
    rw [hmult, Nat.cast_prod]
  have h2 : (n : ℝ) = ∏ p ∈ n.primeFactors, ((p ^ n.factorization p : ℕ) : ℝ) := by
    exact_mod_cast hnfac
  calc ((σ 1 n : ℕ) : ℝ) / n
      = (∏ p ∈ n.primeFactors, ((σ 1 (p ^ n.factorization p) : ℕ) : ℝ)) /
        (∏ p ∈ n.primeFactors, ((p ^ n.factorization p : ℕ) : ℝ)) := by
        rw [← h1, ← h2]
    _ = ∏ p ∈ n.primeFactors,
          ((σ 1 (p ^ n.factorization p) : ℕ) : ℝ) / ((p ^ n.factorization p : ℕ) : ℝ) := by
        rw [Finset.prod_div_distrib]
    _ ≤ ∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
        apply Finset.prod_le_prod
        · intro p _
          positivity
        · intro p hp
          have hpp := Nat.prime_of_mem_primeFactors hp
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
          have hpm : (0 : ℝ) < (p : ℝ) - 1 := by linarith
          have hpe : (0 : ℝ) < ((p ^ n.factorization p : ℕ) : ℝ) := by
            have : 0 < p ^ n.factorization p := pow_pos hpp.pos _
            exact_mod_cast this
          rw [div_le_div_iff₀ hpe hpm]
          have key := sigma_prime_pow_mul_lt hpp (n.factorization p)
          have hpow : (p : ℝ) ^ (n.factorization p + 1) =
              (p : ℝ) * ((p ^ n.factorization p : ℕ) : ℝ) := by
            push_cast
            ring
          rw [hpow] at key
          linarith

/-- Witness for `violator_ratio_ge`: its hypotheses can all hold. `3` is an odd violator
(`σ 3 = 4`, while `(e^γ/2) * 3 * log log 3 ≤ 3`, using `γ < 2/3`, `log 2 > 2/3` and `log x ≤ x - 1`). -/
theorem three_violator : Violator 3 := by
  refine ⟨⟨1, by norm_num⟩, le_refl 3, ?_⟩
  have hσ : ((σ 1 3 : ℕ) : ℝ) = 4 := by
    rw [sigma_one_apply, Nat.Prime.sum_divisors Nat.prime_three]
    norm_num
  rw [hσ]
  have hγ : Real.eulerMascheroniConstant < 2 / 3 := Real.eulerMascheroniConstant_lt_two_thirds
  have hexp2 : Real.exp (2 / 3 : ℝ) < 2 := by
    rw [← Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 2)]
    have := Real.log_two_gt_d9
    norm_num at this ⊢
    linarith
  have hexp : Real.exp Real.eulerMascheroniConstant < 2 :=
    lt_trans (Real.exp_lt_exp.mpr hγ) hexp2
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hℓ : Real.log (Real.log 3) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (lt_trans zero_lt_one one_lt_log_three)
    linarith
  have hℓ0 : 0 ≤ Real.log (Real.log 3) := (Real.log_pos one_lt_log_three).le
  have hE : Real.exp Real.eulerMascheroniConstant / 2 < 1 := by linarith
  have hE0 : 0 ≤ Real.exp Real.eulerMascheroniConstant / 2 := by positivity
  have hprod : Real.exp Real.eulerMascheroniConstant / 2 * Real.log (Real.log 3) ≤ 1 := by
    calc Real.exp Real.eulerMascheroniConstant / 2 * Real.log (Real.log 3) ≤ 1 * 1 :=
          mul_le_mul hE.le hℓ hℓ0 (by norm_num)
      _ = 1 := by norm_num
  push_cast
  nlinarith

/-- Witness for `sigma_div_le_prod`: its hypothesis `n ≠ 0` holds for a nontrivial `n`. -/
theorem sigma_div_le_prod_hyps_satisfiable : ∃ n : ℕ, n ≠ 0 ∧ 1 < n :=
  ⟨6, by norm_num, by norm_num⟩

end SimpleZerosHilbertRobinEpstein.OddRobin
