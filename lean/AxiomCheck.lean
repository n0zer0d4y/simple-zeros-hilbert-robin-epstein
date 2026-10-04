/-
  Axiom check: every theorem should depend only on `propext`, `Classical.choice` and `Quot.sound`
  (no `sorryAx`, no `Lean.ofReduceBool`). Run from `lean/`:  lake env lean AxiomCheck.lean
-/
import SimpleZerosHilbertRobinEpstein

open SimpleZerosHilbertRobinEpstein.SimpleZeros
open SimpleZerosHilbertRobinEpstein.OddRobin

-- Result 1: the block bound, the deduction and the numeric instances
#print axioms WangCell.block_bound
#print axioms WangCell.gram_block_bound
#print axioms WangCell.linear_lower
#print axioms WangCell.simple_on_line_numeric
#print axioms WangCell.simple_on_line_numeric_hyps_satisfiable
#print axioms WangCellLine.line_lower
#print axioms WangCellLine.simple_numeric_H7
#print axioms WangCellLine.distinct_numeric_H7
#print axioms WangCellLine.simple_numeric_H8
#print axioms WangCellLine.distinct_numeric_H8
#print axioms WangCellLine.numeric_H7_hyps_satisfiable
#print axioms WangCellLine.numeric_H8_hyps_satisfiable
#print axioms WangCellAnchor.gap_jensen
#print axioms WangCellAnchor.pair_sum_anchor
#print axioms WangCellAnchor.phi_convex
#print axioms WangCellAnchor.phi_antitone
#print axioms WangCellAnchor.phi_one_lower
#print axioms WangCellAnchor.anchor_H8_numeric
#print axioms WangCellAnchor.pair_sum_anchor_phi
#print axioms WangCellAnchor.pair_sum_anchor_phi_hyps_satisfiable

-- Result 3: the formal core of the odd Robin enumeration
#print axioms violator_ratio_ge
#print axioms sigma_div_le_prod
#print axioms three_violator
#print axioms sigma_div_le_prod_hyps_satisfiable
