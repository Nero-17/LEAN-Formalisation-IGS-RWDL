import RequestProject.Section31.EIGSFlowerRuleGraph
import Mathlib.Data.Finset.Prod

/-! Exact endpoint incidences of the actual flower rule. -/

namespace EIGS
noncomputable section
open scoped Classical

theorem flowerPoint_eq_source (branches segments : ℕ) (branch : Fin branches)
    (position : Fin (segments + 1)) :
    flowerPoint branches segments branch position = Sum.inl false ↔ position.val = 0 := by
  constructor
  · intro equality
    have height := congrArg (flowerHeight branches segments) equality
    rw [flowerPoint_height branches segments branch position] at height
    simpa only [flowerHeight, Bool.false_eq_true, ↓reduceIte] using height
  · intro equality
    simp [flowerPoint, equality]

theorem flowerPoint_eq_sink (branches segments : ℕ) (segmentsPositive : 0 < segments)
    (branch : Fin branches) (position : Fin (segments + 1)) :
    flowerPoint branches segments branch position = Sum.inl true ↔ position.val = segments := by
  constructor
  · intro equality
    have height := congrArg (flowerHeight branches segments) equality
    rw [flowerPoint_height branches segments branch position] at height
    simpa only [flowerHeight, ↓reduceIte] using height
  · intro equality
    simp [flowerPoint, equality, Nat.ne_of_gt segmentsPositive]

theorem flowerGraph_source_tail_iff (branches segments : ℕ)
    (edge : Fin branches × Fin segments) :
    (flowerGraph branches segments).tail edge = Sum.inl false ↔
      edge.1.val ≠ 0 ∧ edge.2.val = 0 := by
  have afterStart : edge.2.val + 1 ≠ 0 := by omega
  by_cases backwards : edge.1.val = 0 <;>
    simp [flowerGraph, flowerEdgeStart, flowerEdgeEnd, flowerPoint_eq_source, backwards, afterStart]

theorem flowerGraph_source_head_iff (branches segments : ℕ)
    (edge : Fin branches × Fin segments) :
    (flowerGraph branches segments).head edge = Sum.inl false ↔
      edge.1.val = 0 ∧ edge.2.val = 0 := by
  have afterStart : edge.2.val + 1 ≠ 0 := by omega
  by_cases backwards : edge.1.val = 0 <;>
    simp [flowerGraph, flowerEdgeStart, flowerEdgeEnd, flowerPoint_eq_source, backwards, afterStart]

theorem flowerGraph_sink_tail_iff (branches segments : ℕ) (segmentsPositive : 0 < segments)
    (edge : Fin branches × Fin segments) :
    (flowerGraph branches segments).tail edge = Sum.inl true ↔
      edge.1.val = 0 ∧ edge.2.val + 1 = segments := by
  have beforeSink : edge.2.val ≠ segments := Nat.ne_of_lt edge.2.isLt
  by_cases backwards : edge.1.val = 0 <;>
    simp [flowerGraph, flowerEdgeStart, flowerEdgeEnd,
      flowerPoint_eq_sink branches segments segmentsPositive, backwards, beforeSink]

theorem flowerGraph_sink_head_iff (branches segments : ℕ) (segmentsPositive : 0 < segments)
    (edge : Fin branches × Fin segments) :
    (flowerGraph branches segments).head edge = Sum.inl true ↔
      edge.1.val ≠ 0 ∧ edge.2.val + 1 = segments := by
  have beforeSink : edge.2.val ≠ segments := Nat.ne_of_lt edge.2.isLt
  by_cases backwards : edge.1.val = 0 <;>
    simp [flowerGraph, flowerEdgeStart, flowerEdgeEnd,
      flowerPoint_eq_sink branches segments segmentsPositive, backwards, beforeSink]

theorem flower_filtered_edges_count (branches segments : ℕ)
    (predicate : Fin branches → Prop) [DecidablePred predicate] (position : Fin segments) :
    (Finset.univ.filter (fun edge : Fin branches × Fin segments =>
      predicate edge.1 ∧ edge.2 = position)).card =
        (Finset.univ.filter predicate).card := by
  have filteredProduct : (Finset.univ.filter (fun edge : Fin branches × Fin segments =>
      predicate edge.1 ∧ edge.2 = position)) =
        (Finset.univ.filter predicate) ×ˢ ({position} : Finset (Fin segments)) := by
    ext edge
    simp
  rw [filteredProduct, Finset.card_product]
  simp

theorem flower_first_branch_count (branches : ℕ) (branchesPositive : 0 < branches) :
    (Finset.univ.filter (fun branch : Fin branches => branch.val = 0)).card = 1 := by
  have filterEquality : (Finset.univ.filter (fun branch : Fin branches => branch.val = 0)) =
      {⟨0, branchesPositive⟩} := by
    ext branch
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact (@Fin.ext_iff branches branch ⟨0, branchesPositive⟩).symm
  rw [filterEquality]
  simp

theorem flower_other_branches_count (branches : ℕ) (branchesPositive : 0 < branches) :
    (Finset.univ.filter (fun branch : Fin branches => branch.val ≠ 0)).card = branches - 1 := by
  have counts := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin branches))) (fun branch : Fin branches => branch.val = 0)
  rw [flower_first_branch_count branches branchesPositive, Finset.card_univ, Fintype.card_fin] at counts
  change 1 + (Finset.univ.filter (fun branch : Fin branches => branch.val ≠ 0)).card = branches at counts
  omega

end
end EIGS

#print axioms EIGS.flowerGraph_source_tail_iff
#print axioms EIGS.flowerGraph_source_head_iff
#print axioms EIGS.flowerGraph_sink_tail_iff
#print axioms EIGS.flowerGraph_sink_head_iff
#print axioms EIGS.flower_filtered_edges_count
#print axioms EIGS.flower_first_branch_count
#print axioms EIGS.flower_other_branches_count
