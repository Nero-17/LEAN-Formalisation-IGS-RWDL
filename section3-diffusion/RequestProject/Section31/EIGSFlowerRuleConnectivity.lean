import RequestProject.Section31.EIGSFlowerRuleGraph

/-! The actual parallel-chain flower graph is connected, and its planting
vertices are nonadjacent when the chains have at least two segments.
These are rule-graph facts, not hypotheses inferred from scalar formulas. -/

namespace EIGS
open SimpleGraph
open scoped Classical
noncomputable section

theorem flowerGraph_edge_adj (branches segments : ℕ) (edge : Fin branches × Fin segments) :
    (ruleSG (flowerSystem branches segments) 0).Adj
      (flowerEdgeStart branches segments edge) (flowerEdgeEnd branches segments edge) := by
  have distinct : flowerEdgeStart branches segments edge ≠ flowerEdgeEnd branches segments edge := by
    intro equality
    have heights := congrArg (flowerHeight branches segments) equality
    simp only [flowerEdgeStart, flowerEdgeEnd, flowerPoint_height] at heights
    omega
  change _ ≠ _ ∧ ((∃ other : Fin branches × Fin segments,
    (flowerGraph branches segments).tail other = flowerEdgeStart branches segments edge ∧
      (flowerGraph branches segments).head other = flowerEdgeEnd branches segments edge) ∨
    (∃ other : Fin branches × Fin segments,
    (flowerGraph branches segments).tail other = flowerEdgeEnd branches segments edge ∧
      (flowerGraph branches segments).head other = flowerEdgeStart branches segments edge))
  refine ⟨distinct, ?_⟩
  by_cases backwards : edge.1.val = 0
  · right
    exact ⟨edge, by simp [flowerGraph, backwards], by simp [flowerGraph, backwards]⟩
  · left
    exact ⟨edge, by simp [flowerGraph, backwards], by simp [flowerGraph, backwards]⟩

theorem flowerPoint_reachable (branches segments : ℕ) (branch : Fin branches)
    (position : Fin (segments + 1)) :
    (ruleSG (flowerSystem branches segments) 0).Reachable (Sum.inl false)
      (flowerPoint branches segments branch position) := by
  have reaches : ∀ index : ℕ, (bound : index ≤ segments) →
      (ruleSG (flowerSystem branches segments) 0).Reachable (Sum.inl false)
        (flowerPoint branches segments branch ⟨index, by omega⟩) := by
    intro index
    induction index with
    | zero =>
      intro bound
      simpa [flowerPoint] using
        (SimpleGraph.Reachable.refl (G := ruleSG (flowerSystem branches segments) 0) (Sum.inl false))
    | succ index induction =>
      intro bound
      have before : index ≤ segments := by omega
      have edge : Fin branches × Fin segments := (branch, ⟨index, by omega⟩)
      have adjacent := flowerGraph_edge_adj branches segments edge
      have joined := (induction before).trans adjacent.reachable
      simpa only [edge, flowerEdgeStart, flowerEdgeEnd] using joined
  exact reaches position.val (by omega)

theorem flowerSystem_connected (branches segments : ℕ)
    (branchesPositive : 0 < branches) (segmentsAtLeastTwo : 2 ≤ segments) (colour : Fin 1) :
    (ruleSG (flowerSystem branches segments) colour).Connected := by
  have colourZero : colour = 0 := Subsingleton.elim _ _
  subst colour
  let initialBranch : Fin branches := ⟨0, branchesPositive⟩
  have reaches (vertex : Bool ⊕ (Fin branches × Fin (segments - 1))) :
      (ruleSG (flowerSystem branches segments) 0).Reachable (Sum.inl false) vertex := by
    cases vertex with
    | inl terminal =>
      cases terminal with
      | false => exact SimpleGraph.Reachable.refl _
      | true =>
        have toSink := flowerPoint_reachable branches segments initialBranch ⟨segments, by omega⟩
        simpa [flowerPoint, show segments ≠ 0 by omega] using toSink
    | inr interior =>
      have toInterior := flowerPoint_reachable branches segments interior.1 ⟨interior.2.val + 1, by omega⟩
      have beforeSink : interior.2.val + 1 ≠ segments := by omega
      simpa [flowerPoint, beforeSink] using toInterior
  exact ⟨fun first second => (reaches first).symm.trans (reaches second)⟩

theorem flowerSystem_plantingNonadjacent (branches segments : ℕ)
    (segmentsAtLeastTwo : 2 ≤ segments) (colour : Fin 1) :
    ¬ (ruleSG (flowerSystem branches segments) colour).Adj
      ((flowerSystem branches segments).plantPlus colour)
      ((flowerSystem branches segments).plantMinus colour) := by
  intro adjacent
  change (Sum.inl false ≠ Sum.inl true) ∧
    ((∃ edge : Fin branches × Fin segments,
      (flowerGraph branches segments).tail edge = Sum.inl false ∧
        (flowerGraph branches segments).head edge = Sum.inl true) ∨
    (∃ edge : Fin branches × Fin segments,
      (flowerGraph branches segments).tail edge = Sum.inl true ∧
        (flowerGraph branches segments).head edge = Sum.inl false)) at adjacent
  rcases adjacent.2 with ⟨edge, tail, head⟩ | ⟨edge, tail, head⟩ <;>
    have heights := flowerGraph_edge_height branches segments edge <;>
    rw [tail, head] at heights <;>
    simp only [flowerHeight, Bool.false_eq_true, ↓reduceIte] at heights <;>
    omega

end
end EIGS

#print axioms EIGS.flowerGraph_edge_adj
#print axioms EIGS.flowerPoint_reachable
#print axioms EIGS.flowerSystem_connected
#print axioms EIGS.flowerSystem_plantingNonadjacent
