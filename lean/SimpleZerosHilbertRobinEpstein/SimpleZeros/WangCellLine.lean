import Mathlib
import SimpleZerosHilbertRobinEpstein.SimpleZeros.WangCellBound

/-!
# The line form of the whole-cell envelope (larger cells)

`WangCellBound.lean` proves `Ψ k ≥ (k - 2) Ψ 3` from `Ψ 4 ≥ 4 Ψ 3`.  For larger cells the certified minima give a line
`Ψ k ≥ s k - t` instead: base cases `k < K` from certified `k`-point minima, an anchor at `K` from the one-dimensional
convex minorant, and superadditivity.  This file proves, with no `sorry`:

* `line_lower`: base cases below `K`, the anchor `s K ≤ Ψ K` and superadditivity give `s k - t ≤ Ψ k` for every `k`;
* `cell_sum_line`: summed over cells, `s (Σ k_c) - t #cells ≤ Σ Ψ(k_c)`;
* `line_proportion_liminf`: Wang's inequality plus the cell bound give `n / N ≥ (C0 - t / H) / (1 - s) - ε` eventually;
* `line_distinct_liminf`: the distinct-zeros version `D / N ≥ (1 + C0) / 2 + (s u - t / H) / 2 - ε`;
* `simple_numeric_H7` and `distinct_numeric_H7`: the numeric instance at `H = 7` with `s = 0.0012194`, `t = 0.0045914`;
* `simple_numeric_H8` and `distinct_numeric_H8`: the numeric instance at `H = 8` with `s = 0.002124`, `t = 0.0096373`,
  anchor `K = 9`, giving the headline bounds `0.672724` and `0.836362`.

The analytic inputs (Wang's Proposition 2.1, the partition step, the asymptotics of `E` and of the number of cells) and the certified
minima enter as hypotheses.  The witnesses at the end instantiate every hypothesis.
-/

namespace SimpleZerosHilbertRobinEpstein.SimpleZeros.WangCellLine

open Finset
open SimpleZerosHilbertRobinEpstein.SimpleZeros.WangCell

/-- The line form of the envelope. -/
theorem line_lower (Ψ : ℕ → ℝ) (s t : ℝ) (K : ℕ) (hK : 0 < K)
    (hsup : ∀ a b, Ψ a + Ψ b ≤ Ψ (a + b))
    (hbase : ∀ k, k < K → s * (k : ℝ) - t ≤ Ψ k)
    (hanchor : s * (K : ℝ) ≤ Ψ K) :
    ∀ k : ℕ, s * (k : ℝ) - t ≤ Ψ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < K
    · exact hbase k hk
    · push_neg at hk
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
      have hj : j < K + j := by omega
      have h1 := ih j hj
      have h2 := hsup K j
      push_cast
      linarith

/-- Summing the line over the cells. -/
theorem cell_sum_line {ι : Type*} (S : Finset ι) (cnt : ι → ℕ) (Ψ : ℕ → ℝ) (s t : ℝ)
    (hline : ∀ k : ℕ, s * (k : ℝ) - t ≤ Ψ k) :
    s * (∑ c ∈ S, (cnt c : ℝ)) - t * S.card ≤ ∑ c ∈ S, Ψ (cnt c) := by
  calc s * (∑ c ∈ S, (cnt c : ℝ)) - t * S.card
      = ∑ c ∈ S, (s * (cnt c : ℝ) - t) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ ∑ c ∈ S, Ψ (cnt c) := Finset.sum_le_sum (fun c _ => hline (cnt c))

/-- Pointwise form with explicit error terms. -/
theorem line_proportion_bound (n N E Δ M s t C0 H ε : ℝ) (ht : 0 ≤ t)
    (hW : 2 * N - E + Δ ≤ n) (hΔ : s * n - t * M ≤ Δ)
    (hE : E ≤ (2 - C0 + ε) * N) (hM : M ≤ (1 / H + ε) * N) :
    (C0 - ε - t * (1 / H + ε)) * N ≤ (1 - s) * n := by
  have hM' : t * M ≤ t * ((1 / H + ε) * N) := mul_le_mul_of_nonneg_left hM ht
  nlinarith

/-- The liminf form of the simple-zeros bound. -/
theorem line_proportion_liminf {α : Type*} (F : Filter α) (n N E Δ M : α → ℝ)
    (C0 H s t : ℝ) (_hH : 0 < H) (hs1 : s < 1) (ht : 0 ≤ t)
    (hN : ∀ᶠ T in F, 0 < N T)
    (hW : ∀ᶠ T in F, 2 * N T - E T + Δ T ≤ n T)
    (hΔ : ∀ᶠ T in F, s * n T - t * M T ≤ Δ T)
    (hE : ∀ ε > 0, ∀ᶠ T in F, E T ≤ (2 - C0 + ε) * N T)
    (hM : ∀ ε > 0, ∀ᶠ T in F, M T ≤ (1 / H + ε) * N T) :
    ∀ ε > 0, ∀ᶠ T in F, (C0 - t / H) / (1 - s) - ε ≤ n T / N T := by
  intro ε hε
  have h1s : 0 < 1 - s := by linarith
  have h1t : 0 < 1 + t := by linarith
  have hε' : 0 < ε * (1 - s) / (1 + t) := div_pos (mul_pos hε h1s) h1t
  filter_upwards [hN, hW, hΔ, hE _ hε', hM _ hε'] with T hNT hWT hΔT hET hMT
  have hp := line_proportion_bound (n T) (N T) (E T) (Δ T) (M T) s t C0 H
    (ε * (1 - s) / (1 + t)) ht hWT hΔT hET hMT
  have hid : ε * (1 - s) / (1 + t) * (1 + t) = ε * (1 - s) :=
    div_mul_cancel₀ _ (ne_of_gt h1t)
  have hb : (C0 - t / H) / (1 - s) * (1 - s) = C0 - t / H :=
    div_mul_cancel₀ _ (ne_of_gt h1s)
  have hidN := congrArg (· * N T) hid
  have hbN := congrArg (· * N T) hb
  simp only at hidN hbN
  have hH' : t * (1 / H) = t / H := by ring
  rw [le_div_iff₀ hNT]
  apply le_of_mul_le_mul_left _ h1s
  nlinarith

/-- The distinct-zeros version, from the simple-zeros bound `u`. -/
theorem line_distinct_liminf {α : Type*} (F : Filter α) (n N E Δ M D : α → ℝ)
    (C0 H s t u : ℝ) (hs0 : 0 ≤ s) (ht : 0 ≤ t)
    (hN : ∀ᶠ T in F, 0 < N T)
    (hn : ∀ ε > 0, ∀ᶠ T in F, u - ε ≤ n T / N T)
    (hD : ∀ᶠ T in F, 3 * N T - E T + Δ T ≤ 2 * D T)
    (hΔ : ∀ᶠ T in F, s * n T - t * M T ≤ Δ T)
    (hE : ∀ ε > 0, ∀ᶠ T in F, E T ≤ (2 - C0 + ε) * N T)
    (hM : ∀ ε > 0, ∀ᶠ T in F, M T ≤ (1 / H + ε) * N T) :
    ∀ ε > 0, ∀ᶠ T in F, (1 + C0) / 2 + (s * u - t / H) / 2 - ε ≤ D T / N T := by
  intro ε hε
  have hden : 0 < 1 + s + t := by linarith
  have hδ : 0 < ε / (1 + s + t) := div_pos hε hden
  filter_upwards [hN, hn _ hδ, hD, hΔ, hE _ hδ, hM _ hδ] with T hNT hnT hDT hΔT hET hMT
  have hn' : (u - ε / (1 + s + t)) * N T ≤ n T := by
    rw [le_div_iff₀ hNT] at hnT
    exact hnT
  have hsn : s * ((u - ε / (1 + s + t)) * N T) ≤ s * n T :=
    mul_le_mul_of_nonneg_left hn' hs0
  have htM : t * M T ≤ t * ((1 / H + ε / (1 + s + t)) * N T) :=
    mul_le_mul_of_nonneg_left hMT ht
  have hid : ε / (1 + s + t) * (1 + s + t) = ε := div_mul_cancel₀ _ (ne_of_gt hden)
  have hidN : ε / (1 + s + t) * (1 + s + t) * N T = ε * N T := by rw [hid]
  have hH' : t * (1 / H) = t / H := by ring
  rw [le_div_iff₀ hNT]
  nlinarith

/-- Numeric instance at `H = 7`: `s = 12194 / 10^7`, `t = 45914 / 10^7`; the hypotheses on `Ψ` are the certified
base cases (`Ψ 4`, `Ψ 5`, `Ψ 6`) and the anchor (`Ψ 8`); `Ψ 7 ≥ Ψ 6` comes from superadditivity. -/
theorem simple_numeric_H7 {α ι : Type*} (F : Filter α)
    (n N E Δ : α → ℝ) (cells : α → Finset ι) (cnt : α → ι → ℕ)
    (Ψ : ℕ → ℝ) (C0 : ℝ) (hC0 : 6725007 / 10000000 ≤ C0)
    (hΨnn : ∀ k, 0 ≤ Ψ k) (hΨsup : ∀ a b, Ψ a + Ψ b ≤ Ψ (a + b))
    (h4 : 2862 / 10000000 ≤ Ψ 4) (h5 : 15056 / 10000000 ≤ Ψ 5)
    (h6 : 6136 / 1000000 ≤ Ψ 6) (h8 : 97552 / 10000000 ≤ Ψ 8)
    (hN : ∀ᶠ T in F, 0 < N T)
    (hcount : ∀ᶠ T in F, (∑ c ∈ cells T, (cnt T c : ℝ)) = n T)
    (hpart : ∀ᶠ T in F, (∑ c ∈ cells T, Ψ (cnt T c)) ≤ Δ T)
    (hW : ∀ᶠ T in F, 2 * N T - E T + Δ T ≤ n T)
    (hE : ∀ ε > 0, ∀ᶠ T in F, E T ≤ (2 - C0 + ε) * N T)
    (hM : ∀ ε > 0, ∀ᶠ T in F, ((cells T).card : ℝ) ≤ (1 / 7 + ε) * N T) :
    ∀ ε > 0, ∀ᶠ T in F, (672665 / 1000000 : ℝ) - ε ≤ n T / N T := by
  have h7 : 6136 / 1000000 ≤ Ψ 7 := by
    have h := hΨsup 6 1
    have h1 := hΨnn 1
    norm_num at h ⊢
    linarith
  have hline : ∀ k : ℕ, (12194 / 10000000 : ℝ) * (k : ℝ) - 45914 / 10000000 ≤ Ψ k := by
    refine line_lower Ψ (12194 / 10000000) (45914 / 10000000) 8 (by norm_num) hΨsup ?_ ?_
    · intro k hk
      interval_cases k
      · have := hΨnn 0; norm_num; linarith
      · have := hΨnn 1; norm_num; linarith
      · have := hΨnn 2; norm_num; linarith
      · have := hΨnn 3; norm_num; linarith
      · norm_num; linarith
      · norm_num; linarith
      · norm_num; linarith
      · norm_num; linarith
    · norm_num; linarith
  have hΔ : ∀ᶠ T in F, (12194 / 10000000 : ℝ) * n T - 45914 / 10000000 * ((cells T).card : ℝ) ≤ Δ T := by
    filter_upwards [hcount, hpart] with T hc hp
    have h := cell_sum_line (cells T) (cnt T) Ψ (12194 / 10000000) (45914 / 10000000) hline
    rw [hc] at h
    linarith
  intro ε hε
  have hmain := line_proportion_liminf F n N E Δ (fun T => ((cells T).card : ℝ)) C0 7
    (12194 / 10000000) (45914 / 10000000) (by norm_num) (by norm_num) (by norm_num) hN hW hΔ hE hM ε hε
  have hnum : (672665 / 1000000 : ℝ) ≤ (C0 - (45914 / 10000000) / 7) / (1 - 12194 / 10000000) := by
    rw [le_div_iff₀ (by norm_num)]
    linarith
  filter_upwards [hmain] with T hT
  linarith

/-- The distinct-zeros numeric instance at `H = 7`. -/
theorem distinct_numeric_H7 {α ι : Type*} (F : Filter α)
    (n N E Δ D : α → ℝ) (cells : α → Finset ι) (cnt : α → ι → ℕ)
    (Ψ : ℕ → ℝ) (C0 : ℝ) (hC0 : 6725007 / 10000000 ≤ C0)
    (hΨnn : ∀ k, 0 ≤ Ψ k) (hΨsup : ∀ a b, Ψ a + Ψ b ≤ Ψ (a + b))
    (h4 : 2862 / 10000000 ≤ Ψ 4) (h5 : 15056 / 10000000 ≤ Ψ 5)
    (h6 : 6136 / 1000000 ≤ Ψ 6) (h8 : 97552 / 10000000 ≤ Ψ 8)
    (hN : ∀ᶠ T in F, 0 < N T)
    (hcount : ∀ᶠ T in F, (∑ c ∈ cells T, (cnt T c : ℝ)) = n T)
    (hpart : ∀ᶠ T in F, (∑ c ∈ cells T, Ψ (cnt T c)) ≤ Δ T)
    (hW : ∀ᶠ T in F, 2 * N T - E T + Δ T ≤ n T)
    (hD : ∀ᶠ T in F, 3 * N T - E T + Δ T ≤ 2 * D T)
    (hE : ∀ ε > 0, ∀ᶠ T in F, E T ≤ (2 - C0 + ε) * N T)
    (hM : ∀ ε > 0, ∀ᶠ T in F, ((cells T).card : ℝ) ≤ (1 / 7 + ε) * N T) :
    ∀ ε > 0, ∀ᶠ T in F, (836332 / 1000000 : ℝ) - ε ≤ D T / N T := by
  have hsimple := simple_numeric_H7 F n N E Δ cells cnt Ψ C0 hC0 hΨnn hΨsup h4 h5 h6 h8 hN hcount hpart hW hE hM
  have h7 : 6136 / 1000000 ≤ Ψ 7 := by
    have h := hΨsup 6 1
    have h1 := hΨnn 1
    norm_num at h ⊢
    linarith
  have hline : ∀ k : ℕ, (12194 / 10000000 : ℝ) * (k : ℝ) - 45914 / 10000000 ≤ Ψ k := by
    refine line_lower Ψ (12194 / 10000000) (45914 / 10000000) 8 (by norm_num) hΨsup ?_ ?_
    · intro k hk
      interval_cases k
      · have := hΨnn 0; norm_num; linarith
      · have := hΨnn 1; norm_num; linarith
      · have := hΨnn 2; norm_num; linarith
      · have := hΨnn 3; norm_num; linarith
      · norm_num; linarith
      · norm_num; linarith
      · norm_num; linarith
      · norm_num; linarith
    · norm_num; linarith
  have hΔ : ∀ᶠ T in F, (12194 / 10000000 : ℝ) * n T - 45914 / 10000000 * ((cells T).card : ℝ) ≤ Δ T := by
    filter_upwards [hcount, hpart] with T hc hp
    have h := cell_sum_line (cells T) (cnt T) Ψ (12194 / 10000000) (45914 / 10000000) hline
    rw [hc] at h
    linarith
  intro ε hε
  have hmain := line_distinct_liminf F n N E Δ (fun T => ((cells T).card : ℝ)) D C0 7
    (12194 / 10000000) (45914 / 10000000) (672665 / 1000000) (by norm_num) (by norm_num) hN hsimple hD hΔ hE hM ε hε
  have hnum : (836332 / 1000000 : ℝ) ≤ (1 + C0) / 2 + ((12194 / 10000000) * (672665 / 1000000) - (45914 / 10000000) / 7) / 2 := by
    linarith
  filter_upwards [hmain] with T hT
  linarith

/-- Numeric instance at `H = 8`: `s = 21240 / 10^7`, `t = 96373 / 10^7`, anchor `K = 9`; the hypotheses on `Ψ` are the certified
base cases (`Ψ 5`, `Ψ 6`, `Ψ 7`) and the anchor (`Ψ 9`); `Ψ 8 ≥ Ψ 7` comes from superadditivity. -/
theorem simple_numeric_H8 {α ι : Type*} (F : Filter α)
    (n N E Δ : α → ℝ) (cells : α → Finset ι) (cnt : α → ι → ℕ)
    (Ψ : ℕ → ℝ) (C0 : ℝ) (hC0 : 6725007 / 10000000 ≤ C0)
    (hΨnn : ∀ k, 0 ≤ Ψ k) (hΨsup : ∀ a b, Ψ a + Ψ b ≤ Ψ (a + b))
    (h5 : 9827 / 10000000 ≤ Ψ 5) (h6 : 31067 / 10000000 ≤ Ψ 6)
    (h7 : 73547 / 10000000 ≤ Ψ 7) (h9 : 19116 / 1000000 ≤ Ψ 9)
    (hN : ∀ᶠ T in F, 0 < N T)
    (hcount : ∀ᶠ T in F, (∑ c ∈ cells T, (cnt T c : ℝ)) = n T)
    (hpart : ∀ᶠ T in F, (∑ c ∈ cells T, Ψ (cnt T c)) ≤ Δ T)
    (hW : ∀ᶠ T in F, 2 * N T - E T + Δ T ≤ n T)
    (hE : ∀ ε > 0, ∀ᶠ T in F, E T ≤ (2 - C0 + ε) * N T)
    (hM : ∀ ε > 0, ∀ᶠ T in F, ((cells T).card : ℝ) ≤ (1 / 8 + ε) * N T) :
    ∀ ε > 0, ∀ᶠ T in F, (672724 / 1000000 : ℝ) - ε ≤ n T / N T := by
  have h8 : 73547 / 10000000 ≤ Ψ 8 := by
    have h := hΨsup 7 1
    have h1 := hΨnn 1
    norm_num at h ⊢
    linarith
  have hline : ∀ k : ℕ, (21240 / 10000000 : ℝ) * (k : ℝ) - 96373 / 10000000 ≤ Ψ k := by
    refine line_lower Ψ (21240 / 10000000) (96373 / 10000000) 9 (by norm_num) hΨsup ?_ ?_
    · intro k hk
      interval_cases k
      · have := hΨnn 0; norm_num; linarith
      · have := hΨnn 1; norm_num; linarith
      · have := hΨnn 2; norm_num; linarith
      · have := hΨnn 3; norm_num; linarith
      · have := hΨnn 4; norm_num; linarith
      · norm_num; linarith
      · norm_num; linarith
      · norm_num; linarith
      · norm_num; linarith
    · norm_num; linarith
  have hΔ : ∀ᶠ T in F, (21240 / 10000000 : ℝ) * n T - 96373 / 10000000 * ((cells T).card : ℝ) ≤ Δ T := by
    filter_upwards [hcount, hpart] with T hc hp
    have h := cell_sum_line (cells T) (cnt T) Ψ (21240 / 10000000) (96373 / 10000000) hline
    rw [hc] at h
    linarith
  intro ε hε
  have hmain := line_proportion_liminf F n N E Δ (fun T => ((cells T).card : ℝ)) C0 8
    (21240 / 10000000) (96373 / 10000000) (by norm_num) (by norm_num) (by norm_num) hN hW hΔ hE hM ε hε
  have hnum : (672724 / 1000000 : ℝ) ≤ (C0 - (96373 / 10000000) / 8) / (1 - 21240 / 10000000) := by
    rw [le_div_iff₀ (by norm_num)]
    linarith
  filter_upwards [hmain] with T hT
  linarith

/-- The distinct-zeros numeric instance at `H = 8`. -/
theorem distinct_numeric_H8 {α ι : Type*} (F : Filter α)
    (n N E Δ D : α → ℝ) (cells : α → Finset ι) (cnt : α → ι → ℕ)
    (Ψ : ℕ → ℝ) (C0 : ℝ) (hC0 : 6725007 / 10000000 ≤ C0)
    (hΨnn : ∀ k, 0 ≤ Ψ k) (hΨsup : ∀ a b, Ψ a + Ψ b ≤ Ψ (a + b))
    (h5 : 9827 / 10000000 ≤ Ψ 5) (h6 : 31067 / 10000000 ≤ Ψ 6)
    (h7 : 73547 / 10000000 ≤ Ψ 7) (h9 : 19116 / 1000000 ≤ Ψ 9)
    (hN : ∀ᶠ T in F, 0 < N T)
    (hcount : ∀ᶠ T in F, (∑ c ∈ cells T, (cnt T c : ℝ)) = n T)
    (hpart : ∀ᶠ T in F, (∑ c ∈ cells T, Ψ (cnt T c)) ≤ Δ T)
    (hW : ∀ᶠ T in F, 2 * N T - E T + Δ T ≤ n T)
    (hD : ∀ᶠ T in F, 3 * N T - E T + Δ T ≤ 2 * D T)
    (hE : ∀ ε > 0, ∀ᶠ T in F, E T ≤ (2 - C0 + ε) * N T)
    (hM : ∀ ε > 0, ∀ᶠ T in F, ((cells T).card : ℝ) ≤ (1 / 8 + ε) * N T) :
    ∀ ε > 0, ∀ᶠ T in F, (836362 / 1000000 : ℝ) - ε ≤ D T / N T := by
  have hsimple := simple_numeric_H8 F n N E Δ cells cnt Ψ C0 hC0 hΨnn hΨsup h5 h6 h7 h9 hN hcount hpart hW hE hM
  have h8 : 73547 / 10000000 ≤ Ψ 8 := by
    have h := hΨsup 7 1
    have h1 := hΨnn 1
    norm_num at h ⊢
    linarith
  have hline : ∀ k : ℕ, (21240 / 10000000 : ℝ) * (k : ℝ) - 96373 / 10000000 ≤ Ψ k := by
    refine line_lower Ψ (21240 / 10000000) (96373 / 10000000) 9 (by norm_num) hΨsup ?_ ?_
    · intro k hk
      interval_cases k
      · have := hΨnn 0; norm_num; linarith
      · have := hΨnn 1; norm_num; linarith
      · have := hΨnn 2; norm_num; linarith
      · have := hΨnn 3; norm_num; linarith
      · have := hΨnn 4; norm_num; linarith
      · norm_num; linarith
      · norm_num; linarith
      · norm_num; linarith
      · norm_num; linarith
    · norm_num; linarith
  have hΔ : ∀ᶠ T in F, (21240 / 10000000 : ℝ) * n T - 96373 / 10000000 * ((cells T).card : ℝ) ≤ Δ T := by
    filter_upwards [hcount, hpart] with T hc hp
    have h := cell_sum_line (cells T) (cnt T) Ψ (21240 / 10000000) (96373 / 10000000) hline
    rw [hc] at h
    linarith
  intro ε hε
  have hmain := line_distinct_liminf F n N E Δ (fun T => ((cells T).card : ℝ)) D C0 8
    (21240 / 10000000) (96373 / 10000000) (672724 / 1000000) (by norm_num) (by norm_num) hN hsimple hD hΔ hE hM ε hε
  have hnum : (836362 / 1000000 : ℝ) ≤ (1 + C0) / 2 + ((21240 / 10000000) * (672724 / 1000000) - (96373 / 10000000) / 8) / 2 := by
    linarith
  filter_upwards [hmain] with T hT
  linarith

/-! ## Witnesses -/

lemma psiEx_five : psiEx 5 = 9 / 2000 := by
  unfold psiEx
  have h : max (((5 : ℕ) : ℝ) - 2) 0 = 3 := by
    rw [max_eq_left] <;> norm_num
  rw [h]
  norm_num

lemma psiEx_six : psiEx 6 = 16 / 2000 := by
  unfold psiEx
  have h : max (((6 : ℕ) : ℝ) - 2) 0 = 4 := by
    rw [max_eq_left] <;> norm_num
  rw [h]
  norm_num

lemma psiEx_eight : psiEx 8 = 36 / 2000 := by
  unfold psiEx
  have h : max (((8 : ℕ) : ℝ) - 2) 0 = 6 := by
    rw [max_eq_left] <;> norm_num
  rw [h]
  norm_num

lemma psiEx_four' : psiEx 4 = 4 / 2000 := psiEx_four

/-- The hypotheses of `simple_numeric_H7` and `distinct_numeric_H7` are satisfiable: `M = T + 1` cells of five points,
`N = 7 M`, `n = 5 M`, `E = 9.1 M`, `Δ = M Ψ(5)`, `D = 6 M`, with the profile `psiEx`. -/
theorem numeric_H7_hyps_satisfiable :
    (∀ ε > 0, ∀ᶠ (T : ℕ) in Filter.atTop,
      (672665 / 1000000 : ℝ) - ε ≤ (5 * ((T : ℝ) + 1)) / (7 * ((T : ℝ) + 1))) ∧
    (∀ ε > 0, ∀ᶠ (T : ℕ) in Filter.atTop,
      (836332 / 1000000 : ℝ) - ε ≤ (6 * ((T : ℝ) + 1)) / (7 * ((T : ℝ) + 1))) := by
  have common : ∀ ε > 0, ∀ᶠ (T : ℕ) in Filter.atTop,
      (672665 / 1000000 : ℝ) - ε ≤ (5 * ((T : ℝ) + 1)) / (7 * ((T : ℝ) + 1)) := by
    exact simple_numeric_H7 (F := (Filter.atTop : Filter ℕ))
      (n := fun T : ℕ => 5 * ((T : ℝ) + 1)) (N := fun T : ℕ => 7 * ((T : ℝ) + 1))
      (E := fun T : ℕ => (91 / 10 : ℝ) * ((T : ℝ) + 1))
      (Δ := fun T : ℕ => ((T : ℝ) + 1) * (9 / 2000))
      (cells := fun T : ℕ => Finset.range (T + 1)) (cnt := fun _ _ => 5)
      (Ψ := psiEx) (C0 := 6725007 / 10000000)
      (by norm_num) psiEx_nonneg psi_example_superadditive
      (by rw [psiEx_four]; norm_num) (by rw [psiEx_five]; norm_num)
      (by rw [psiEx_six]; norm_num) (by rw [psiEx_eight]; norm_num)
      (Filter.Eventually.of_forall (fun T => by positivity))
      (Filter.Eventually.of_forall (fun T => by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring))
      (Filter.Eventually.of_forall (fun T => by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, psiEx_five]
        push_cast
        linarith))
      (Filter.Eventually.of_forall (fun T => by
        have hT : (0 : ℝ) ≤ (T : ℝ) + 1 := by positivity
        nlinarith))
      (fun ε hε => Filter.Eventually.of_forall (fun T => by
        have hT : (0 : ℝ) ≤ (T : ℝ) + 1 := by positivity
        nlinarith))
      (fun ε hε => Filter.Eventually.of_forall (fun T => by
        have hT : (0 : ℝ) ≤ (T : ℝ) + 1 := by positivity
        simp only [Finset.card_range]
        push_cast
        nlinarith))
  refine ⟨common, ?_⟩
  exact distinct_numeric_H7 (F := (Filter.atTop : Filter ℕ))
    (n := fun T : ℕ => 5 * ((T : ℝ) + 1)) (N := fun T : ℕ => 7 * ((T : ℝ) + 1))
    (E := fun T : ℕ => (91 / 10 : ℝ) * ((T : ℝ) + 1))
    (Δ := fun T : ℕ => ((T : ℝ) + 1) * (9 / 2000)) (D := fun T : ℕ => 6 * ((T : ℝ) + 1))
    (cells := fun T : ℕ => Finset.range (T + 1)) (cnt := fun _ _ => 5)
    (Ψ := psiEx) (C0 := 6725007 / 10000000)
    (by norm_num) psiEx_nonneg psi_example_superadditive
    (by rw [psiEx_four]; norm_num) (by rw [psiEx_five]; norm_num)
    (by rw [psiEx_six]; norm_num) (by rw [psiEx_eight]; norm_num)
    (Filter.Eventually.of_forall (fun T => by positivity))
    (Filter.Eventually.of_forall (fun T => by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring))
    (Filter.Eventually.of_forall (fun T => by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, psiEx_five]
      push_cast
      linarith))
    (Filter.Eventually.of_forall (fun T => by
      have hT : (0 : ℝ) ≤ (T : ℝ) + 1 := by positivity
      nlinarith))
    (Filter.Eventually.of_forall (fun T => by
      have hT : (0 : ℝ) ≤ (T : ℝ) + 1 := by positivity
      nlinarith))
    (fun ε hε => Filter.Eventually.of_forall (fun T => by
      have hT : (0 : ℝ) ≤ (T : ℝ) + 1 := by positivity
      nlinarith))
    (fun ε hε => Filter.Eventually.of_forall (fun T => by
      have hT : (0 : ℝ) ≤ (T : ℝ) + 1 := by positivity
      simp only [Finset.card_range]
      push_cast
      nlinarith))

lemma psiEx_seven : psiEx 7 = 25 / 2000 := by
  unfold psiEx
  have h : max (((7 : ℕ) : ℝ) - 2) 0 = 5 := by
    rw [max_eq_left] <;> norm_num
  rw [h]
  norm_num

lemma psiEx_nine : psiEx 9 = 49 / 2000 := by
  unfold psiEx
  have h : max (((9 : ℕ) : ℝ) - 2) 0 = 7 := by
    rw [max_eq_left] <;> norm_num
  rw [h]
  norm_num

/-- The hypotheses of `simple_numeric_H8` and `distinct_numeric_H8` are satisfiable: `M = T + 1` cells of six points,
`N = 8 M`, `n = 6 M`, `E = 10.1 M`, `Δ = M Ψ(6)`, `D = 7 M`, with the profile `psiEx`. -/
theorem numeric_H8_hyps_satisfiable :
    (∀ ε > 0, ∀ᶠ (T : ℕ) in Filter.atTop,
      (672724 / 1000000 : ℝ) - ε ≤ (6 * ((T : ℝ) + 1)) / (8 * ((T : ℝ) + 1))) ∧
    (∀ ε > 0, ∀ᶠ (T : ℕ) in Filter.atTop,
      (836362 / 1000000 : ℝ) - ε ≤ (7 * ((T : ℝ) + 1)) / (8 * ((T : ℝ) + 1))) := by
  have common : ∀ ε > 0, ∀ᶠ (T : ℕ) in Filter.atTop,
      (672724 / 1000000 : ℝ) - ε ≤ (6 * ((T : ℝ) + 1)) / (8 * ((T : ℝ) + 1)) := by
    exact simple_numeric_H8 (F := (Filter.atTop : Filter ℕ))
      (n := fun T : ℕ => 6 * ((T : ℝ) + 1)) (N := fun T : ℕ => 8 * ((T : ℝ) + 1))
      (E := fun T : ℕ => (101 / 10 : ℝ) * ((T : ℝ) + 1))
      (Δ := fun T : ℕ => ((T : ℝ) + 1) * (16 / 2000))
      (cells := fun T : ℕ => Finset.range (T + 1)) (cnt := fun _ _ => 6)
      (Ψ := psiEx) (C0 := 6725007 / 10000000)
      (by norm_num) psiEx_nonneg psi_example_superadditive
      (by rw [psiEx_five]; norm_num) (by rw [psiEx_six]; norm_num)
      (by rw [psiEx_seven]; norm_num) (by rw [psiEx_nine]; norm_num)
      (Filter.Eventually.of_forall (fun T => by positivity))
      (Filter.Eventually.of_forall (fun T => by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring))
      (Filter.Eventually.of_forall (fun T => by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, psiEx_six]
        push_cast
        linarith))
      (Filter.Eventually.of_forall (fun T => by
        have hT : (0 : ℝ) ≤ (T : ℝ) + 1 := by positivity
        nlinarith))
      (fun ε hε => Filter.Eventually.of_forall (fun T => by
        have hT : (0 : ℝ) ≤ (T : ℝ) + 1 := by positivity
        nlinarith))
      (fun ε hε => Filter.Eventually.of_forall (fun T => by
        have hT : (0 : ℝ) ≤ (T : ℝ) + 1 := by positivity
        simp only [Finset.card_range]
        push_cast
        nlinarith))
  refine ⟨common, ?_⟩
  exact distinct_numeric_H8 (F := (Filter.atTop : Filter ℕ))
    (n := fun T : ℕ => 6 * ((T : ℝ) + 1)) (N := fun T : ℕ => 8 * ((T : ℝ) + 1))
    (E := fun T : ℕ => (101 / 10 : ℝ) * ((T : ℝ) + 1))
    (Δ := fun T : ℕ => ((T : ℝ) + 1) * (16 / 2000)) (D := fun T : ℕ => 7 * ((T : ℝ) + 1))
    (cells := fun T : ℕ => Finset.range (T + 1)) (cnt := fun _ _ => 6)
    (Ψ := psiEx) (C0 := 6725007 / 10000000)
    (by norm_num) psiEx_nonneg psi_example_superadditive
    (by rw [psiEx_five]; norm_num) (by rw [psiEx_six]; norm_num)
    (by rw [psiEx_seven]; norm_num) (by rw [psiEx_nine]; norm_num)
    (Filter.Eventually.of_forall (fun T => by positivity))
    (Filter.Eventually.of_forall (fun T => by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring))
    (Filter.Eventually.of_forall (fun T => by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, psiEx_six]
      push_cast
      linarith))
    (Filter.Eventually.of_forall (fun T => by
      have hT : (0 : ℝ) ≤ (T : ℝ) + 1 := by positivity
      nlinarith))
    (Filter.Eventually.of_forall (fun T => by
      have hT : (0 : ℝ) ≤ (T : ℝ) + 1 := by positivity
      nlinarith))
    (fun ε hε => Filter.Eventually.of_forall (fun T => by
      have hT : (0 : ℝ) ≤ (T : ℝ) + 1 := by positivity
      nlinarith))
    (fun ε hε => Filter.Eventually.of_forall (fun T => by
      have hT : (0 : ℝ) ≤ (T : ℝ) + 1 := by positivity
      simp only [Finset.card_range]
      push_cast
      nlinarith))

end SimpleZerosHilbertRobinEpstein.SimpleZeros.WangCellLine
