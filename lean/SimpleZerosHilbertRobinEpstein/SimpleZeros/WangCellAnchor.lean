import Mathlib

/-!
# The adjacent-gap anchor and the concrete minorant

The list `phiLines` is, as exact rationals, the list of 40 lines in
`code/01-simple-zeros-critical-line/targets-H7-H8.json`, which `oned_check.py` certifies below `K_0^2` on `[0, 1.06]`.

* `gap_jensen`, `adjacent_le_pairs`, `pair_sum_anchor`: `k = m + 1` points whose `m` adjacent gaps sum to at most `H` have pair sum at least
  `m φ(H / m)` for a convex antitone minorant `φ`;
* `lineMax_convex`, `lineMax_antitone`, `lineMax_ge`, `phi_convex`, `phi_antitone`, `phi_one_lower`: the concrete `φ = max(0, 40 lines)`;
* `anchor_H8_numeric`: `9 s ≤ min 1 (16 φ(1))` for `s = 21240/10^7`;
* `pair_sum_anchor_phi`: the anchor for the concrete `φ`, only `φ ≤ h` on `[0, ∞)` (the certified inequality `φ ≤ K_0^2`) remains a hypothesis.
-/

namespace SimpleZerosHilbertRobinEpstein.SimpleZeros.WangCellAnchor

open Finset

/-! ## The adjacent-gap anchor

The anchor `s K ≤ Ψ_K` of the line form comes
from `k` points crowded into a cell: their `k - 1` adjacent gaps sum to at most `H`, so by Jensen
for a convex minorant `φ` of `K_0^2` (antitone on `[0, ∞)`), the pair sum is at least
`(k - 1) φ(H / (k - 1))`. -/

/-- Jensen over the gaps: `Σ h(g_i) ≥ m φ(L / m)` when `Σ g_i ≤ L`. -/
theorem gap_jensen {m : ℕ} (hm : 0 < m) (φ h : ℝ → ℝ) (hconv : ConvexOn ℝ (Set.Ici 0) φ)
    (hanti : AntitoneOn φ (Set.Ici 0)) (hle : ∀ y, 0 ≤ y → φ y ≤ h y)
    (g : Fin m → ℝ) (hg : ∀ i, 0 ≤ g i) (L : ℝ) (hL : ∑ i, g i ≤ L) :
    (m : ℝ) * φ (L / m) ≤ ∑ i, h (g i) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hw : ∑ _i : Fin m, (1 : ℝ) / m = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_one_div_cancel hmR.ne'
  have hJ := hconv.map_sum_le (t := Finset.univ) (w := fun _ => (1 : ℝ) / m) (p := g)
    (fun _ _ => by positivity) hw (fun i _ => hg i)
  simp only [smul_eq_mul] at hJ
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hJ
  have hsum0 : 0 ≤ ∑ i, g i := Finset.sum_nonneg (fun i _ => hg i)
  have hmean : 1 / (m : ℝ) * ∑ i, g i ≤ L / m := by
    rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right hL hmR.le
  have hmean0 : (0 : ℝ) ≤ 1 / (m : ℝ) * ∑ i, g i := mul_nonneg (by positivity) hsum0
  have hL0 : (0 : ℝ) ≤ L / m := div_nonneg (le_trans hsum0 hL) hmR.le
  have hφ : φ (L / m) ≤ φ (1 / (m : ℝ) * ∑ i, g i) := hanti hmean0 hL0 hmean
  have hh : ∑ i, φ (g i) ≤ ∑ i, h (g i) := Finset.sum_le_sum (fun i _ => hle _ (hg i))
  have key : φ (L / m) ≤ 1 / (m : ℝ) * ∑ i, h (g i) :=
    calc φ (L / m) ≤ φ (1 / (m : ℝ) * ∑ i, g i) := hφ
      _ ≤ 1 / (m : ℝ) * ∑ i, φ (g i) := hJ
      _ ≤ 1 / (m : ℝ) * ∑ i, h (g i) := mul_le_mul_of_nonneg_left hh (by positivity)
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hmR] at key
  linarith

/-- With `h ≥ 0`, the pair sum over points `x_0, …, x_m` is at least the adjacent-pair sum. -/
theorem adjacent_le_pairs {m : ℕ} (x : Fin (m + 1) → ℝ) (h : ℝ → ℝ) (hnn : ∀ y, 0 ≤ h y) :
    ∑ i : Fin m, h (x i.succ - x i.castSucc) ≤
      ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), if i < j then h (x j - x i) else 0 := by
  have hterm : ∀ i j : Fin (m + 1), 0 ≤ (if i < j then h (x j - x i) else 0) := by
    intro i j
    split_ifs
    · exact hnn _
    · exact le_refl 0
  have hrow : ∀ i : Fin m, h (x i.succ - x i.castSucc) ≤
      ∑ j : Fin (m + 1), if i.castSucc < j then h (x j - x i.castSucc) else 0 := by
    intro i
    have hlt : i.castSucc < i.succ := Fin.castSucc_lt_succ
    have hs := Finset.single_le_sum (f := fun j : Fin (m + 1) =>
      if i.castSucc < j then h (x j - x i.castSucc) else 0) (fun j _ => hterm _ j)
      (Finset.mem_univ i.succ)
    simp only [if_pos hlt] at hs
    exact hs
  have hlast : 0 ≤ ∑ j : Fin (m + 1), if Fin.last m < j then h (x j - x (Fin.last m)) else 0 :=
    Finset.sum_nonneg (fun j _ => hterm _ j)
  have hsplit := Fin.sum_univ_castSucc
    (fun i : Fin (m + 1) => ∑ j : Fin (m + 1), if i < j then h (x j - x i) else 0)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => hrow i)
  linarith

/-- The anchor: `k = m + 1` points whose `m` adjacent gaps sum to at most `H` have pair sum at
least `m φ(H / m)`. -/
theorem pair_sum_anchor {m : ℕ} (hm : 0 < m) (x : Fin (m + 1) → ℝ)
    (hx : ∀ i : Fin m, x i.castSucc ≤ x i.succ) (H : ℝ)
    (hH : ∑ i : Fin m, (x i.succ - x i.castSucc) ≤ H) (φ h : ℝ → ℝ)
    (hconv : ConvexOn ℝ (Set.Ici 0) φ) (hanti : AntitoneOn φ (Set.Ici 0))
    (hle : ∀ y, 0 ≤ y → φ y ≤ h y) (hnn : ∀ y, 0 ≤ h y) :
    (m : ℝ) * φ (H / m) ≤
      ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), if i < j then h (x j - x i) else 0 :=
  le_trans (gap_jensen hm φ h hconv hanti hle (fun i => x i.succ - x i.castSucc)
    (fun i => sub_nonneg.mpr (hx i)) H hH) (adjacent_le_pairs x h hnn)

/-! ## The concrete minorant `φ` of `K_0^2`

`φ` is the maximum of `0` and the 40 lines of `code/01-simple-zeros-critical-line/targets-H7-H8.json`;
`oned_check.py` certifies `φ ≤ K_0^2` on `[0, 1.06]` with ball arithmetic. Here: `φ` is convex and antitone, `φ(1)` is bounded below, and
the `H = 8` anchor `9 s ≤ min 1 (16 φ(1))` holds for `s = 21240 / 10^7`. -/

/-- The maximum of `0` and the lines `a + m g` for `(a, m)` in `L`. -/
noncomputable def lineMax (L : List (ℝ × ℝ)) (g : ℝ) : ℝ :=
  L.foldr (fun p acc => max (p.1 + p.2 * g) acc) 0

theorem lineMax_convex (L : List (ℝ × ℝ)) : ConvexOn ℝ Set.univ (lineMax L) := by
  induction L with
  | nil =>
    refine ⟨convex_univ, fun x _ y _ α β hα hβ hαβ => ?_⟩
    simp [lineMax]
  | cons p L ih =>
    refine ⟨convex_univ, fun x _ y _ α β hα hβ hαβ => ?_⟩
    have hR := ih.2 (Set.mem_univ x) (Set.mem_univ y) hα hβ hαβ
    simp only [smul_eq_mul] at hR ⊢
    show max (p.1 + p.2 * (α * x + β * y)) (lineMax L (α * x + β * y)) ≤
      α * max (p.1 + p.2 * x) (lineMax L x) + β * max (p.1 + p.2 * y) (lineMax L y)
    have h1 : p.1 + p.2 * x ≤ max (p.1 + p.2 * x) (lineMax L x) := le_max_left _ _
    have h2 : p.1 + p.2 * y ≤ max (p.1 + p.2 * y) (lineMax L y) := le_max_left _ _
    have h3 : lineMax L x ≤ max (p.1 + p.2 * x) (lineMax L x) := le_max_right _ _
    have h4 : lineMax L y ≤ max (p.1 + p.2 * y) (lineMax L y) := le_max_right _ _
    have e : p.1 = α * p.1 + β * p.1 := by linear_combination (-p.1) * hαβ
    apply max_le
    · linarith [mul_le_mul_of_nonneg_left h1 hα, mul_le_mul_of_nonneg_left h2 hβ]
    · linarith [mul_le_mul_of_nonneg_left h3 hα, mul_le_mul_of_nonneg_left h4 hβ]

theorem lineMax_antitone (L : List (ℝ × ℝ)) (hL : ∀ p ∈ L, p.2 ≤ 0) :
    Antitone (lineMax L) := by
  induction L with
  | nil =>
    intro x y _
    simp [lineMax]
  | cons p L ih =>
    intro x y hxy
    have hp : p.2 ≤ 0 := hL p (by simp)
    have ih' := ih (fun q hq => hL q (by simp [hq])) hxy
    show max (p.1 + p.2 * y) (lineMax L y) ≤ max (p.1 + p.2 * x) (lineMax L x)
    have hm : p.2 * y ≤ p.2 * x := mul_le_mul_of_nonpos_left hxy hp
    exact max_le_max (by linarith) ih'

theorem lineMax_ge (L : List (ℝ × ℝ)) (p : ℝ × ℝ) (hp : p ∈ L) (g : ℝ) :
    p.1 + p.2 * g ≤ lineMax L g := by
  induction L with
  | nil => simp at hp
  | cons q L ih =>
    show p.1 + p.2 * g ≤ max (q.1 + q.2 * g) (lineMax L g)
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact le_max_left _ _
    · exact le_trans (ih hp') (le_max_right _ _)

/-- The 40 lines of the certified minorant (intercepts already lowered by `1e-6`). -/
noncomputable def phiLines : List (ℝ × ℝ) :=
  [((99999899 : ℝ) / 100000000, -(59786391 : ℝ) / 50000000),
   ((97776009 : ℝ) / 100000000, -(7263787 : ℝ) / 6250000),
   ((95458433 : ℝ) / 100000000, -(14097523 : ℝ) / 12500000),
   ((5817389 : ℝ) / 6250000, -(109299637 : ℝ) / 100000000),
   ((90614823 : ℝ) / 100000000, -(105750519 : ℝ) / 100000000),
   ((88097923 : ℝ) / 100000000, -(6386061 : ℝ) / 6250000),
   ((5344123 : ℝ) / 6250000, -(12318693 : ℝ) / 12500000),
   ((20717591 : ℝ) / 25000000, -(47456537 : ℝ) / 50000000),
   ((80168689 : ℝ) / 100000000, -(91237311 : ℝ) / 100000000),
   ((77433809 : ℝ) / 100000000, -(87567439 : ℝ) / 100000000),
   ((4665161 : ℝ) / 6250000, -(5242041 : ℝ) / 6250000),
   ((1436581 : ℝ) / 2000000, -(80198109 : ℝ) / 100000000),
   ((13793901 : ℝ) / 20000000, -(76512689 : ℝ) / 100000000),
   ((16524727 : ℝ) / 25000000, -(72861157 : ℝ) / 100000000),
   ((31596557 : ℝ) / 50000000, -(17303081 : ℝ) / 25000000),
   ((60287701 : ℝ) / 100000000, -(65610231 : ℝ) / 100000000),
   ((11471653 : ℝ) / 20000000, -(62023831 : ℝ) / 100000000),
   ((10888139 : ℝ) / 20000000, -(58496129 : ℝ) / 100000000),
   ((51510491 : ℝ) / 100000000, -(5499643 : ℝ) / 10000000),
   ((24301773 : ℝ) / 50000000, -(5156641 : ℝ) / 10000000),
   ((5711929 : ℝ) / 12500000, -(24087963 : ℝ) / 50000000),
   ((42821741 : ℝ) / 100000000, -(22432527 : ℝ) / 50000000),
   ((39958279 : ℝ) / 100000000, -(4160439 : ℝ) / 10000000),
   ((37140037 : ℝ) / 100000000, -(19216081 : ℝ) / 50000000),
   ((17171609 : ℝ) / 50000000, -(17659939 : ℝ) / 50000000),
   ((31601919 : ℝ) / 100000000, -(32303703 : ℝ) / 100000000),
   ((28892899 : ℝ) / 100000000, -(7339053 : ℝ) / 25000000),
   ((6562269 : ℝ) / 25000000, -(13255657 : ℝ) / 50000000),
   ((23647917 : ℝ) / 100000000, -(11871397 : ℝ) / 50000000),
   ((21120899 : ℝ) / 100000000, -(10541073 : ℝ) / 50000000),
   ((9323169 : ℝ) / 50000000, -(3700897 : ℝ) / 20000000),
   ((16254019 : ℝ) / 100000000, -(16038761 : ℝ) / 100000000),
   ((6961621 : ℝ) / 50000000, -(546461 : ℝ) / 4000000),
   ((11681877 : ℝ) / 100000000, -(11399083 : ℝ) / 100000000),
   ((1188791 : ℝ) / 12500000, -(9229509 : ℝ) / 100000000),
   ((3717173 : ℝ) / 50000000, -(7176393 : ℝ) / 100000000),
   ((108711 : ℝ) / 2000000, -(1304851 : ℝ) / 25000000),
   ((707479 : ℝ) / 20000000, -(211211 : ℝ) / 6250000),
   ((430703 : ℝ) / 25000000, -(204703 : ℝ) / 12500000),
   ((4203 : ℝ) / 100000000, -(4071 : ℝ) / 100000000)]

theorem phi_convex : ConvexOn ℝ (Set.Ici 0) (lineMax phiLines) :=
  (lineMax_convex phiLines).subset (Set.subset_univ _) (convex_Ici 0)

theorem phi_antitone : AntitoneOn (lineMax phiLines) (Set.Ici 0) :=
  (lineMax_antitone phiLines (by norm_num [phiLines])).antitoneOn _

/-- `φ(1)` is at least the value of its best line at `1`. -/
theorem phi_one_lower : ((141397 : ℝ) / 50000000) ≤ lineMax phiLines 1 :=
  le_trans (by norm_num) (lineMax_ge phiLines ((11681877 : ℝ) / 100000000, -(11399083 : ℝ) / 100000000) (by simp [phiLines]) 1)

/-- The `H = 8` anchor of the line `s = 21240 / 10^7`: nine points in a cell
of length `8` have `Ψ_9 ≥ min 1 (2 · 8 φ(1)) ≥ 9 s`. -/
theorem anchor_H8_numeric : 9 * ((21240 : ℝ) / 10000000) ≤ min 1 (16 * lineMax phiLines 1) := by
  have h := phi_one_lower
  apply le_min
  · norm_num
  · linarith

/-- `pair_sum_anchor` for the concrete `φ`: only `φ ≤ h` on `[0, ∞)` remains a hypothesis. -/
theorem pair_sum_anchor_phi {m : ℕ} (hm : 0 < m) (x : Fin (m + 1) → ℝ)
    (hx : ∀ i : Fin m, x i.castSucc ≤ x i.succ) (H : ℝ)
    (hH : ∑ i : Fin m, (x i.succ - x i.castSucc) ≤ H) (h : ℝ → ℝ)
    (hle : ∀ y, 0 ≤ y → lineMax phiLines y ≤ h y) (hnn : ∀ y, 0 ≤ h y) :
    (m : ℝ) * lineMax phiLines (H / m) ≤
      ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), if i < j then h (x j - x i) else 0 :=
  pair_sum_anchor hm x hx H hH (lineMax phiLines) h phi_convex phi_antitone hle hnn

theorem lineMax_nonneg (L : List (ℝ × ℝ)) (g : ℝ) : 0 ≤ lineMax L g := by
  induction L with
  | nil => simp [lineMax]
  | cons p L ih =>
    show 0 ≤ max (p.1 + p.2 * g) (lineMax L g)
    exact le_trans ih (le_max_right _ _)

/-- The hypotheses of `pair_sum_anchor_phi` can all hold: `m = 1`, the points `0` and `1`, `H = 1`, `h = φ` itself. -/
theorem pair_sum_anchor_phi_hyps_satisfiable :
    ((1 : ℕ) : ℝ) * lineMax phiLines ((1 : ℝ) / ((1 : ℕ) : ℝ)) ≤
      ∑ i : Fin (1 + 1), ∑ j : Fin (1 + 1),
        if i < j then lineMax phiLines (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) else 0 := by
  exact pair_sum_anchor_phi (m := 1) (by norm_num) (fun k : Fin (1 + 1) => ((k : ℕ) : ℝ))
    (by intro i; fin_cases i; simp)
    (1 : ℝ) (by simp [Fin.sum_univ_one])
    (lineMax phiLines) (fun y _ => le_refl _) (fun y => lineMax_nonneg phiLines y)

/-- A second witness: `gap_jensen` with `φ = h = φ` itself and two gaps of length `1/2`. -/
theorem gap_jensen_hyps_satisfiable :
    ((2 : ℕ) : ℝ) * lineMax phiLines ((1 : ℝ) / ((2 : ℕ) : ℝ)) ≤ ∑ i : Fin 2, lineMax phiLines ((fun _ : Fin 2 => (1 : ℝ) / 2) i) := by
  exact gap_jensen (m := 2) (by norm_num) (lineMax phiLines) (lineMax phiLines) phi_convex phi_antitone
    (fun y _ => le_refl _) (fun _ => (1 : ℝ) / 2) (fun _ => by norm_num) 1 (by simp [Fin.sum_univ_two])

end SimpleZerosHilbertRobinEpstein.SimpleZeros.WangCellAnchor
