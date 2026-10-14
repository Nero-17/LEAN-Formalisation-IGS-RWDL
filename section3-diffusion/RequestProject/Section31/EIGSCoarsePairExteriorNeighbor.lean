import RequestProject.Section31.EIGSAddressSupport
import RequestProject.Section31.EIGSVertexInclusion
import RequestProject.Section2VertexGrowth

/-! Every actual coarse graph of positive level has at least three distinct
vertices. Connectivity therefore forces an exterior neighbour of either
endpoint of every pair. This supplies the actual two-endpoint escape geometry,
not a presumed probability bound. Candidate source. -/

namespace IGS.Sec31
open scoped Classical
variable {Vertex : Type*}

theorem connected_pair_has_exterior_neighbor (graph : SimpleGraph Vertex)
    (connected : graph.Connected) (first second third : Vertex)
    (thirdFirst : third ≠ first) (thirdSecond : third ≠ second) :
    ∃ endpoint exterior : Vertex,
      (endpoint = first ∨ endpoint = second) ∧ exterior ≠ first ∧ exterior ≠ second ∧
        graph.Adj endpoint exterior := by
  by_contra none
  have preservesPair : ∀ source target,
      (source = first ∨ source = second) → graph.Adj source target →
      (target = first ∨ target = second) := by
    intro source target inside adjacent
    by_contra outside
    exact none ⟨source, target, inside, (fun equal => outside (Or.inl equal)),
      (fun equal => outside (Or.inr equal)), adjacent⟩
  have walkPreservesPair : ∀ {source target} (walk : graph.Walk source target),
      (source = first ∨ source = second) → (target = first ∨ target = second) := by
    intro source target walk
    induction walk with
    | nil => exact id
    | cons adjacent walk induction =>
      intro inside
      exact induction (preservesPair _ _ inside adjacent)
  obtain ⟨walk, _⟩ := connected.exists_walk_length_eq_dist first third
  rcases walkPreservesPair walk (Or.inl rfl) with equal | equal
  · exact thirdFirst equal
  · exact thirdSecond equal

theorem exists_outside_pair_of_three_distinct {first second third : Vertex}
    (firstSecond : first ≠ second) (firstThird : first ≠ third) (secondThird : second ≠ third)
    (left right : Vertex) : ∃ outside : Vertex, outside ≠ left ∧ outside ≠ right := by
  by_contra none
  have eachInside (vertex : Vertex) : vertex = left ∨ vertex = right := by
    by_cases atLeft : vertex = left
    · exact Or.inl atLeft
    · exact Or.inr (by by_contra atRight; exact none ⟨vertex, atLeft, atRight⟩)
  rcases eachInside first with equalFirst | equalFirst <;>
    rcases eachInside second with equalSecond | equalSecond <;>
    rcases eachInside third with equalThird | equalThird <;> aesop

end IGS.Sec31

namespace EIGS
open IGS.Sec31
open scoped Classical
noncomputable section
variable {K : ℕ}

theorem xiPositiveCoarse_pair_has_exterior_neighbor (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (coarse : ℕ) (coarsePositive : 1 ≤ coarse) (first second : XiVtx system coarse) :
    ∃ endpoint exterior : XiVtx system coarse,
      (endpoint = first ∨ endpoint = second) ∧ exterior ≠ first ∧ exterior ≠ second ∧
        (XiSimpleGraph system coarse).Adj endpoint exterior := by
  obtain ⟨edge, _⟩ := xiVertex_has_incident_edge system rulesConnected 0 true
  let interior := Classical.choice (rule_interior_nonempty system rulesConnected plantingNonadjacent
    (XiCol system.toRuleData 0 edge))
  let firstFine : XiVtx system 1 := Sum.inl true
  let secondFine : XiVtx system 1 := Sum.inl false
  let thirdFine : XiVtx system 1 := Sum.inr ⟨edge, interior⟩
  have firstSecond : firstFine ≠ secondFine := by
    intro equality
    exact Bool.noConfusion (Sum.inl.inj equality)
  have firstThird : firstFine ≠ thirdFine := by
    intro equality
    change (Sum.inl true : XiVtx system 1) = Sum.inr ⟨edge, interior⟩ at equality
    cases equality
  have secondThird : secondFine ≠ thirdFine := by
    intro equality
    change (Sum.inl false : XiVtx system 1) = Sum.inr ⟨edge, interior⟩ at equality
    cases equality
  have embeddingInjective : Function.Injective (xiVertexInclusion system 1 coarse coarsePositive) := by
    intro left right same
    apply xiVertexEmbedding_injective system 1
    rw [← xiVertexEmbedding_inclusion system 1 coarse coarsePositive left,
      ← xiVertexEmbedding_inclusion system 1 coarse coarsePositive right]
    exact congrArg (xiVertexEmbedding system coarse) same
  obtain ⟨outside, outsideFirst, outsideSecond⟩ := exists_outside_pair_of_three_distinct
    (embeddingInjective.ne firstSecond) (embeddingInjective.ne firstThird) (embeddingInjective.ne secondThird)
    first second
  exact connected_pair_has_exterior_neighbor (XiSimpleGraph system coarse)
    (xiSimpleGraph_connected system rulesConnected coarse) first second outside outsideFirst outsideSecond

end
end EIGS

#print axioms IGS.Sec31.connected_pair_has_exterior_neighbor
#print axioms IGS.Sec31.exists_outside_pair_of_three_distinct
#print axioms EIGS.xiPositiveCoarse_pair_has_exterior_neighbor
