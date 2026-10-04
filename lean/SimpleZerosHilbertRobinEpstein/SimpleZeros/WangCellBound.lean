import Mathlib

/-!
# The finite core of the whole-cell improvement of Wang's simple-on-line bound

The two certified minima are in `certificates/01-simple-zeros-critical-line/cells-H4.json`; the
argument is in `papers/01-simple-zeros-critical-line/main.md`.

Setting (Wang, arXiv:2609.24167, Proposition 2.1): `n ≥ 2N - E + Δ`, where
`Δ = tr Ψ(G)` and `Ψ(t) = (t - 1)^2` on `t ≤ 2`, `2t - 3` beyond. The simple real
elements are partitioned into cells of length `H`; `Ψ_k` is the minimum of `tr Ψ`
over `k` points in one cell. This file proves, with no `sorry`:

* `block_bound`: `Σ Ψ(λ_i) ≥ min(1, Σ (λ_i - 1)^2)` (the Lemma 3.1 argument);
* `linear_lower`: a nonnegative superadditive `Ψ : ℕ → ℝ` with `Ψ 4 ≥ 4 Ψ 3`
  satisfies `Ψ k ≥ (k - 2) Ψ 3` for every `k`;
* `cell_sum_lower`: summed over cells, `Σ_c Ψ(k_c) ≥ Ψ 3 (Σ k_c - 2 #cells)`;
* `proportion_bound`, `proportion_liminf`: Wang's inequality plus the cell bound
  give `n / N ≥ (C0 - 2 Ψ3 / H) / (1 - Ψ3) - ε` eventually, for every `ε > 0`;
* `simple_on_line_liminf`: the composed statement, from the analytic inputs;
* `simple_on_line_numeric`: with `C0 ≥ 0.6725007`, `Ψ 3 ≥ 0.00044386`, `H = 4`,
  eventually `n / N ≥ 0.672577 - ε`.

The analytic inputs (Wang's Proposition 2.1, the partition step, the asymptotics of
`E` and of the number of cells) and the two certified minima enter as hypotheses.
-/

namespace SimpleZerosHilbertRobinEpstein.SimpleZeros.WangCell

open Finset

/-- Wang's function `Ψ(t) = (t - 1)^2` for `t ≤ 2`, `2t - 3` for `t > 2`. -/
noncomputable def psi (t : ℝ) : ℝ := if t ≤ 2 then (t - 1) ^ 2 else 2 * t - 3

lemma psi_nonneg (t : ℝ) : 0 ≤ psi t := by
  unfold psi
  split_ifs with h
  · positivity
  · push_neg at h
    linarith

/-- Block bound (the argument of Wang's Lemma 3.1): if every eigenvalue is at most 2,
`Σ Ψ(λ_i) = Σ (λ_i - 1)^2`; if one exceeds 2, that term alone is above 1. -/
theorem block_bound {κ : Type*} [Fintype κ] (lam : κ → ℝ) :
    min 1 (∑ i, (lam i - 1) ^ 2) ≤ ∑ i, psi (lam i) := by
  by_cases h : ∀ i, lam i ≤ 2
  · have hs : ∑ i, psi (lam i) = ∑ i, (lam i - 1) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [psi, if_pos (h i)]
    rw [hs]
    exact min_le_right _ _
  · push_neg at h
    obtain ⟨j, hj⟩ := h
    have h1 : 1 ≤ psi (lam j) := by
      simp only [psi, if_neg (not_le.mpr hj)]
      linarith
    have hsum : psi (lam j) ≤ ∑ i, psi (lam i) :=
      Finset.single_le_sum (f := fun i => psi (lam i)) (fun i _ => psi_nonneg (lam i))
        (Finset.mem_univ j)
    exact le_trans (min_le_left _ _) (le_trans h1 hsum)

/-- The envelope lemma: superadditivity and `Ψ 4 ≥ 4 Ψ 3` force `Ψ k ≥ (k - 2) Ψ 3`. -/
theorem linear_lower (Ψ : ℕ → ℝ) (hnn : ∀ k, 0 ≤ Ψ k)
    (hsup : ∀ a b, Ψ a + Ψ b ≤ Ψ (a + b)) (h4 : 4 * Ψ 3 ≤ Ψ 4) :
    ∀ k : ℕ, ((k : ℝ) - 2) * Ψ 3 ≤ Ψ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | _ | _ | _ | j
    · have h0 := hnn 0
      have h3 := hnn 3
      norm_num
      linarith
    · have h1 := hnn 1
      have h3 := hnn 3
      norm_num
      linarith
    · have h2 := hnn 2
      norm_num
      linarith
    · norm_num
    · have hj := ih j (by omega)
      have hs : Ψ j + Ψ 4 ≤ Ψ (j + 1 + 1 + 1 + 1) := hsup j 4
      push_cast
      linarith

/-- Summing the envelope lemma over the cells. -/
theorem cell_sum_lower {ι : Type*} (s : Finset ι) (cnt : ι → ℕ) (Ψ : ℕ → ℝ)
    (hlin : ∀ k : ℕ, ((k : ℝ) - 2) * Ψ 3 ≤ Ψ k) :
    Ψ 3 * ((∑ c ∈ s, (cnt c : ℝ)) - 2 * s.card) ≤ ∑ c ∈ s, Ψ (cnt c) := by
  calc Ψ 3 * ((∑ c ∈ s, (cnt c : ℝ)) - 2 * s.card)
      = ∑ c ∈ s, ((cnt c : ℝ) - 2) * Ψ 3 := by
        rw [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ ∑ c ∈ s, Ψ (cnt c) := Finset.sum_le_sum (fun c _ => hlin (cnt c))

/-- Wang's inequality plus the cell bound, rearranged. -/
theorem deduction (n N E Δ M ψ3 : ℝ) (hW : 2 * N - E + Δ ≤ n)
    (hΔ : ψ3 * (n - 2 * M) ≤ Δ) :
    2 * N - E - 2 * ψ3 * M ≤ (1 - ψ3) * n := by
  linarith

/-- Pointwise form with explicit error terms. -/
theorem proportion_bound (n N E Δ M ψ3 C0 H ε : ℝ) (hψ0 : 0 ≤ ψ3)
    (hW : 2 * N - E + Δ ≤ n) (hΔ : ψ3 * (n - 2 * M) ≤ Δ)
    (hE : E ≤ (2 - C0 + ε) * N) (hM : M ≤ (1 / H + ε) * N) :
    (C0 - ε - 2 * ψ3 * (1 / H + ε)) * N ≤ (1 - ψ3) * n := by
  have hd := deduction n N E Δ M ψ3 hW hΔ
  have hM' : ψ3 * M ≤ ψ3 * ((1 / H + ε) * N) := mul_le_mul_of_nonneg_left hM hψ0
  nlinarith

/-- The liminf form: for every `ε > 0`, eventually
`n / N ≥ (C0 - 2 Ψ3 / H) / (1 - Ψ3) - ε`. -/
theorem proportion_liminf {α : Type*} (F : Filter α) (n N E Δ M : α → ℝ)
    (C0 H ψ3 : ℝ) (hH : 0 < H) (hψ0 : 0 ≤ ψ3) (hψ1 : ψ3 < 1)
    (hN : ∀ᶠ T in F, 0 < N T)
    (hW : ∀ᶠ T in F, 2 * N T - E T + Δ T ≤ n T)
    (hΔ : ∀ᶠ T in F, ψ3 * (n T - 2 * M T) ≤ Δ T)
    (hE : ∀ ε > 0, ∀ᶠ T in F, E T ≤ (2 - C0 + ε) * N T)
    (hM : ∀ ε > 0, ∀ᶠ T in F, M T ≤ (1 / H + ε) * N T) :
    ∀ ε > 0, ∀ᶠ T in F, (C0 - 2 * ψ3 / H) / (1 - ψ3) - ε ≤ n T / N T := by
  intro ε hε
  have h1ψ : 0 < 1 - ψ3 := by linarith
  have h12ψ : 0 < 1 + 2 * ψ3 := by linarith
  have hε' : 0 < ε * (1 - ψ3) / (1 + 2 * ψ3) := div_pos (mul_pos hε h1ψ) h12ψ
  filter_upwards [hN, hW, hΔ, hE _ hε', hM _ hε'] with T hNT hWT hΔT hET hMT
  have hp := proportion_bound (n T) (N T) (E T) (Δ T) (M T) ψ3 C0 H
    (ε * (1 - ψ3) / (1 + 2 * ψ3)) hψ0 hWT hΔT hET hMT
  have hid : ε * (1 - ψ3) / (1 + 2 * ψ3) * (1 + 2 * ψ3) = ε * (1 - ψ3) :=
    div_mul_cancel₀ _ (ne_of_gt h12ψ)
  have hb : (C0 - 2 * ψ3 / H) / (1 - ψ3) * (1 - ψ3) = C0 - 2 * ψ3 / H :=
    div_mul_cancel₀ _ (ne_of_gt h1ψ)
  have hidN := congrArg (· * N T) hid
  have hbN := congrArg (· * N T) hb
  simp only at hidN hbN
  have hH' : 2 * ψ3 * (1 / H) = 2 * ψ3 / H := by ring
  rw [le_div_iff₀ hNT]
  apply le_of_mul_le_mul_left _ h1ψ
  nlinarith

/-- The composed statement: from the analytic inputs (Wang's inequality, the partition
step, the asymptotics of `E` and of the number of cells) and the envelope hypotheses on
`Ψ`, the proportion `n / N` is eventually at least `(C0 - 2 Ψ3 / H) / (1 - Ψ3) - ε`. -/
theorem simple_on_line_liminf {α ι : Type*} (F : Filter α)
    (n N E Δ : α → ℝ) (cells : α → Finset ι) (cnt : α → ι → ℕ)
    (Ψ : ℕ → ℝ) (C0 H : ℝ) (hH : 0 < H)
    (hΨnn : ∀ k, 0 ≤ Ψ k) (hΨsup : ∀ a b, Ψ a + Ψ b ≤ Ψ (a + b))
    (hΨ4 : 4 * Ψ 3 ≤ Ψ 4) (hΨ1 : Ψ 3 < 1)
    (hN : ∀ᶠ T in F, 0 < N T)
    (hcount : ∀ᶠ T in F, (∑ c ∈ cells T, (cnt T c : ℝ)) = n T)
    (hpart : ∀ᶠ T in F, (∑ c ∈ cells T, Ψ (cnt T c)) ≤ Δ T)
    (hW : ∀ᶠ T in F, 2 * N T - E T + Δ T ≤ n T)
    (hE : ∀ ε > 0, ∀ᶠ T in F, E T ≤ (2 - C0 + ε) * N T)
    (hM : ∀ ε > 0, ∀ᶠ T in F, ((cells T).card : ℝ) ≤ (1 / H + ε) * N T) :
    ∀ ε > 0, ∀ᶠ T in F, (C0 - 2 * Ψ 3 / H) / (1 - Ψ 3) - ε ≤ n T / N T := by
  have hlin := linear_lower Ψ hΨnn hΨsup hΨ4
  have hΔ : ∀ᶠ T in F, Ψ 3 * (n T - 2 * ((cells T).card : ℝ)) ≤ Δ T := by
    filter_upwards [hcount, hpart] with T hc hp
    have h := cell_sum_lower (cells T) (cnt T) Ψ hlin
    rw [hc] at h
    linarith
  exact proportion_liminf F n N E Δ (fun T => ((cells T).card : ℝ)) C0 H (Ψ 3) hH
    (hΨnn 3) hΨ1 hN hW hΔ hE hM

/-- The arithmetic of the numeric instance at `H = 4`. -/
theorem numeric_instance (C0 ψ3 : ℝ) (hC0 : 6725007 / 10000000 ≤ C0)
    (hψ : 44386 / 100000000 ≤ ψ3) (hψ1 : ψ3 < 1) :
    (672577 / 1000000 : ℝ) ≤ (C0 - 2 * ψ3 / 4) / (1 - ψ3) := by
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- Numeric corollary at `H = 4`: with `C0 ≥ 0.6725007` (the Montgomery-Taylor constant
`3/2 - (1/√2) cot(1/√2)`) and `Ψ 3 ≥ 0.00044386` (twice the certified three-point
minimum, `cells-H4.json`), and `Ψ 4 ≥ 4 Ψ 3` (from the certified
four-point minimum, `cells-H4.json`), the proportion of simple
on-line zeros is eventually at least `0.672577 - ε`. -/
theorem simple_on_line_numeric {α ι : Type*} (F : Filter α)
    (n N E Δ : α → ℝ) (cells : α → Finset ι) (cnt : α → ι → ℕ)
    (Ψ : ℕ → ℝ) (C0 : ℝ)
    (hC0 : 6725007 / 10000000 ≤ C0) (hΨ3 : 44386 / 100000000 ≤ Ψ 3)
    (hΨnn : ∀ k, 0 ≤ Ψ k) (hΨsup : ∀ a b, Ψ a + Ψ b ≤ Ψ (a + b))
    (hΨ4 : 4 * Ψ 3 ≤ Ψ 4) (hΨ1 : Ψ 3 < 1)
    (hN : ∀ᶠ T in F, 0 < N T)
    (hcount : ∀ᶠ T in F, (∑ c ∈ cells T, (cnt T c : ℝ)) = n T)
    (hpart : ∀ᶠ T in F, (∑ c ∈ cells T, Ψ (cnt T c)) ≤ Δ T)
    (hW : ∀ᶠ T in F, 2 * N T - E T + Δ T ≤ n T)
    (hE : ∀ ε > 0, ∀ᶠ T in F, E T ≤ (2 - C0 + ε) * N T)
    (hM : ∀ ε > 0, ∀ᶠ T in F, ((cells T).card : ℝ) ≤ (1 / 4 + ε) * N T) :
    ∀ ε > 0, ∀ᶠ T in F, (672577 / 1000000 : ℝ) - ε ≤ n T / N T := by
  intro ε hε
  have hmain := simple_on_line_liminf F n N E Δ cells cnt Ψ C0 4 (by norm_num)
    hΨnn hΨsup hΨ4 hΨ1 hN hcount hpart hW hE hM ε hε
  have hnum := numeric_instance C0 (Ψ 3) hC0 hΨ3 hΨ1
  filter_upwards [hmain] with T hT
  linarith

/-! ## The Gram-matrix form of the block bound

For the Gram block `B_ij = K(x_i - x_j)` of a
cell, `B` is real symmetric with unit diagonal (`K(0) = 1`), and Wang's `tr Ψ(B)` is
`Σ Ψ(λ_i)` over its eigenvalues. The identity `Σ (λ_i - 1)^2 = Σ_{i ≠ j} B_ij^2` turns
`block_bound` into `tr Ψ(B) ≥ min(1, Σ_{i ≠ j} B_ij^2) = min(1, 2 Σ_{i<j} K(x_i - x_j)^2)`. -/

section Gram

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Conjugating a diagonal matrix by a unitary does not change the trace of `(B - 1)^2`. -/
lemma trace_conj_diag (B U : Matrix n n ℝ) (d : n → ℝ) (hsU : star U * U = 1)
    (hUs : U * star U = 1) (hBe : B = U * diagonal d * star U) :
    ((B - 1) * (B - 1)).trace = ∑ i, (d i - 1) ^ 2 := by
  have hdiag1 : diagonal (fun i => d i - 1) = diagonal d - 1 := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
  have hsub : B - 1 = U * diagonal (fun i => d i - 1) * star U := by
    rw [hdiag1, mul_sub, sub_mul, mul_one, hUs, ← hBe]
  have hsq : (B - 1) * (B - 1)
      = U * (diagonal (fun i => d i - 1) * diagonal (fun i => d i - 1)) * star U := by
    rw [hsub]
    calc U * diagonal (fun i => d i - 1) * star U * (U * diagonal (fun i => d i - 1) * star U)
        = U * diagonal (fun i => d i - 1) * (star U * U) * diagonal (fun i => d i - 1)
            * star U := by simp only [mul_assoc]
      _ = U * (diagonal (fun i => d i - 1) * diagonal (fun i => d i - 1)) * star U := by
          rw [hsU, mul_one]
          simp only [mul_assoc]
  rw [hsq, Matrix.trace_mul_cycle, hsU, one_mul, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- For a real symmetric matrix, `Σ (λ_i - 1)^2 = Σ_{i,j} (B - 1)_ij^2`. -/
theorem sum_sq_eigenvalues_sub_one (B : Matrix n n ℝ) (hB : B.IsHermitian) :
    ∑ i, (hB.eigenvalues i - 1) ^ 2 = ∑ i, ∑ j, (B - 1) i j ^ 2 := by
  have h := hB.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  have h1 := trace_conj_diag B (hB.eigenvectorUnitary : Matrix n n ℝ)
    (RCLike.ofReal ∘ hB.eigenvalues) (Unitary.coe_star_mul_self hB.eigenvectorUnitary)
    (Unitary.coe_mul_star_self hB.eigenvectorUnitary) h
  have h1' : ((B - 1) * (B - 1)).trace = ∑ i, (hB.eigenvalues i - 1) ^ 2 := by
    rw [h1]
    rfl
  have hC : (B - 1).IsHermitian := hB.sub Matrix.isHermitian_one
  have h2 : ((B - 1) * (B - 1)).trace = ∑ i, ∑ j, (B - 1) i j ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [← hC.apply j i, star_trivial, sq]
  exact h1'.symm.trans h2

/-- With unit diagonal, the Frobenius sum of `B - 1` is the off-diagonal sum of `B`. -/
theorem offdiag_sum (B : Matrix n n ℝ) (hdiag : ∀ i, B i i = 1) :
    ∑ i, ∑ j, (B - 1) i j ^ 2 = ∑ i, ∑ j ∈ Finset.univ.erase i, B i j ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have h0 : (B - 1) i i = 0 := by
    rw [Matrix.sub_apply, Matrix.one_apply_eq, hdiag i, sub_self]
  rw [h0, zero_pow two_ne_zero, zero_add]
  apply Finset.sum_congr rfl
  intro j hj
  have hij : i ≠ j := fun h => Finset.ne_of_mem_erase hj h.symm
  rw [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero]

/-- Wang's Lemma 3.1 step for a Gram block: `tr Ψ(B) ≥ min(1, Σ_{i ≠ j} B_ij^2)`. -/
theorem gram_block_bound (B : Matrix n n ℝ) (hB : B.IsHermitian) (hdiag : ∀ i, B i i = 1) :
    min 1 (∑ i, ∑ j ∈ Finset.univ.erase i, B i j ^ 2) ≤ ∑ i, psi (hB.eigenvalues i) := by
  have h := block_bound hB.eigenvalues
  rw [sum_sq_eigenvalues_sub_one B hB, offdiag_sum B hdiag] at h
  exact h

end Gram

/-! ## Witnesses

The hypotheses of the numeric corollary can all hold: `M = T + 1` cells with three points each,
`N = 4 M`, `Ψ k = (1/2000) (max (k - 2) 0)^2` (superadditive, `Ψ 3 = 1/2000`, `Ψ 4 = 4 Ψ 3`), `Δ = M Ψ 3`,
`E = (5 + Ψ 3) M`, `n = 3 M`, `C0 = 6725007 / 10^7`. -/

/-- The example profile `Ψ k = (1/2000) (max (k - 2) 0)^2`. -/
noncomputable def psiEx (k : ℕ) : ℝ := (1 / 2000 : ℝ) * (max ((k : ℝ) - 2) 0) ^ 2

lemma psiEx_three : psiEx 3 = 1 / 2000 := by
  unfold psiEx
  have h : max (((3 : ℕ) : ℝ) - 2) 0 = 1 := by
    rw [max_eq_left] <;> norm_num
  rw [h]
  norm_num

lemma psiEx_four : psiEx 4 = 4 / 2000 := by
  unfold psiEx
  have h : max (((4 : ℕ) : ℝ) - 2) 0 = 2 := by
    rw [max_eq_left] <;> norm_num
  rw [h]
  norm_num

lemma psiEx_nonneg (k : ℕ) : 0 ≤ psiEx k := by
  unfold psiEx
  positivity

/-- `psiEx` is superadditive. -/
theorem psi_example_superadditive (a b : ℕ) : psiEx a + psiEx b ≤ psiEx (a + b) := by
  unfold psiEx
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  push_cast
  rcases le_total (a : ℝ) 2 with h1 | h1 <;> rcases le_total (b : ℝ) 2 with h2 | h2
  · rw [max_eq_right (by linarith : (a : ℝ) - 2 ≤ 0), max_eq_right (by linarith : (b : ℝ) - 2 ≤ 0)]
    have : (0 : ℝ) ≤ max ((a : ℝ) + b - 2) 0 := le_max_right _ _
    nlinarith
  · rw [max_eq_right (by linarith : (a : ℝ) - 2 ≤ 0), max_eq_left (by linarith : (0 : ℝ) ≤ (b : ℝ) - 2),
      max_eq_left (by linarith : (0 : ℝ) ≤ (a : ℝ) + b - 2)]
    nlinarith
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ (a : ℝ) - 2), max_eq_right (by linarith : (b : ℝ) - 2 ≤ 0),
      max_eq_left (by linarith : (0 : ℝ) ≤ (a : ℝ) + b - 2)]
    nlinarith
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ (a : ℝ) - 2), max_eq_left (by linarith : (0 : ℝ) ≤ (b : ℝ) - 2),
      max_eq_left (by linarith : (0 : ℝ) ≤ (a : ℝ) + b - 2)]
    nlinarith

/-- The hypotheses of `simple_on_line_numeric` are satisfiable: a concrete instance, and its conclusion. -/
theorem simple_on_line_numeric_hyps_satisfiable :
    ∀ ε > 0, ∀ᶠ (T : ℕ) in Filter.atTop,
      (672577 / 1000000 : ℝ) - ε ≤ (3 * ((T : ℝ) + 1)) / (4 * ((T : ℝ) + 1)) := by
  have h := simple_on_line_numeric (F := (Filter.atTop : Filter ℕ))
    (n := fun T : ℕ => 3 * ((T : ℝ) + 1)) (N := fun T : ℕ => 4 * ((T : ℝ) + 1))
    (E := fun T : ℕ => (5 + 1 / 2000) * ((T : ℝ) + 1)) (Δ := fun T : ℕ => ((T : ℝ) + 1) * (1 / 2000))
    (cells := fun T : ℕ => Finset.range (T + 1)) (cnt := fun _ _ => 3)
    (Ψ := psiEx) (C0 := 6725007 / 10000000)
    (by norm_num)
    (by rw [psiEx_three]; norm_num)
    psiEx_nonneg
    psi_example_superadditive
    (by rw [psiEx_three, psiEx_four]; norm_num)
    (by rw [psiEx_three]; norm_num)
    (Filter.Eventually.of_forall (fun T => by positivity))
    (Filter.Eventually.of_forall (fun T => by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring))
    (Filter.Eventually.of_forall (fun T => by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, psiEx_three]
      push_cast
      linarith))
    (Filter.Eventually.of_forall (fun T => by ring_nf; exact le_refl _))
    (fun ε hε => Filter.Eventually.of_forall (fun T => by
      have hT : (0 : ℝ) ≤ (T : ℝ) + 1 := by positivity
      nlinarith))
    (fun ε hε => Filter.Eventually.of_forall (fun T => by
      have hT : (0 : ℝ) ≤ (T : ℝ) + 1 := by positivity
      simp only [Finset.card_range]
      push_cast
      nlinarith))
  exact h

end SimpleZerosHilbertRobinEpstein.SimpleZeros.WangCell
