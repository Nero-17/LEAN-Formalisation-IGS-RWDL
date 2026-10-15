import RequestProject.Section31.EIGSVertexDescendants

/-! The actual normal form of substituted vertices records their unique
coarse ancestor cell. Two distinct coarse cells can share a fine vertex only
at their forwarded coarse terminals. No metric or probability hypothesis is
needed for this combinatorial statement. -/

namespace EIGS
open scoped Classical
noncomputable section
variable {K : ℕ}

def xiCoarseCellVertex (system : EIGSData K) (coarse steps : ℕ)
    (ancestor : XiEdge system.toRuleData coarse) (vertex : XiVtx system (coarse + steps)) : Prop :=
  xiVertexAncestorEdge system coarse steps vertex = some ancestor ∨
    vertex = xiForward system coarse steps (XiTail system coarse ancestor) ∨
    vertex = xiForward system coarse steps (XiHead system coarse ancestor)

theorem xiVertexAncestorEdge_forward_none (system : EIGSData K) (coarse steps : ℕ)
    (vertex : XiVtx system coarse) :
    xiVertexAncestorEdge system coarse steps (xiForward system coarse steps vertex) = none := by
  induction steps with
  | zero => rfl
  | succ steps induction => exact induction

theorem xiDescendant_endpoints_coarseCellVertex (system : EIGSData K) (coarse steps : ℕ)
    (edge : XiEdge system.toRuleData (coarse + steps)) :
    xiCoarseCellVertex system coarse steps (xiEdgeAncestor system coarse steps edge)
      (XiTail system (coarse + steps) edge) ∧
    xiCoarseCellVertex system coarse steps (xiEdgeAncestor system coarse steps edge)
      (XiHead system (coarse + steps) edge) := by
  induction steps with
  | zero => exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩
  | succ steps induction =>
      have parent := induction edge.1
      have lift (vertex : XiVtx system (coarse + steps))
          (membership : xiCoarseCellVertex system coarse steps
            (xiEdgeAncestor system coarse steps edge.1) vertex) :
          xiCoarseCellVertex system coarse (steps + 1)
            (xiEdgeAncestor system coarse (steps + 1) edge) (Sum.inl vertex) := by
        rcases membership with interior | tail | head
        · exact Or.inl interior
        · exact Or.inr (Or.inl (congrArg Sum.inl tail))
        · exact Or.inr (Or.inr (congrArg Sum.inl head))
      have embedded (vertex : (system.rule (XiCol system.toRuleData (coarse + steps) edge.1)).V) :
          xiCoarseCellVertex system coarse (steps + 1)
            (xiEdgeAncestor system coarse (steps + 1) edge)
            (embedRuleVtx system (coarse + steps) edge.1
              (XiTail system (coarse + steps) edge.1) (XiHead system (coarse + steps) edge.1) vertex) := by
        by_cases plus : vertex = system.plantPlus (XiCol system.toRuleData (coarse + steps) edge.1)
        · subst vertex
          rw [embedRuleVtx_plantPlus]
          exact lift _ parent.1
        · by_cases minus : vertex = system.plantMinus (XiCol system.toRuleData (coarse + steps) edge.1)
          · subst vertex
            rw [embedRuleVtx_plantMinus]
            exact lift _ parent.2
          · rw [embedRuleVtx_interior system (coarse + steps) edge.1 _ _ plus minus]
            exact Or.inl rfl
      exact ⟨embedded _, embedded _⟩

theorem xiDistinctCoarseCells_common_endpoint_is_boundary (system : EIGSData K)
    (coarse steps : ℕ) (first second : XiEdge system.toRuleData (coarse + steps))
    (distinct : xiEdgeAncestor system coarse steps first ≠ xiEdgeAncestor system coarse steps second)
    (vertex : XiVtx system (coarse + steps))
    (firstIncident : XiTail system (coarse + steps) first = vertex ∨
      XiHead system (coarse + steps) first = vertex)
    (secondIncident : XiTail system (coarse + steps) second = vertex ∨
      XiHead system (coarse + steps) second = vertex) :
    (vertex = xiForward system coarse steps
        (XiTail system coarse (xiEdgeAncestor system coarse steps first)) ∨
      vertex = xiForward system coarse steps
        (XiHead system coarse (xiEdgeAncestor system coarse steps first))) ∧
    (vertex = xiForward system coarse steps
        (XiTail system coarse (xiEdgeAncestor system coarse steps second)) ∨
      vertex = xiForward system coarse steps
        (XiHead system coarse (xiEdgeAncestor system coarse steps second))) := by
  have classified (edge : XiEdge system.toRuleData (coarse + steps))
      (incident : XiTail system (coarse + steps) edge = vertex ∨
        XiHead system (coarse + steps) edge = vertex) :
      xiCoarseCellVertex system coarse steps (xiEdgeAncestor system coarse steps edge) vertex := by
    rcases incident with tail | head
    · simpa only [tail] using (xiDescendant_endpoints_coarseCellVertex system coarse steps edge).1
    · simpa only [head] using (xiDescendant_endpoints_coarseCellVertex system coarse steps edge).2
  have firstClass := classified first firstIncident
  have secondClass := classified second secondIncident
  have boundaryNone {edge : XiEdge system.toRuleData coarse}
      (boundary : vertex = xiForward system coarse steps (XiTail system coarse edge) ∨
        vertex = xiForward system coarse steps (XiHead system coarse edge)) :
      xiVertexAncestorEdge system coarse steps vertex = none := by
    rcases boundary with tail | head
    · rw [tail]
      exact xiVertexAncestorEdge_forward_none system coarse steps _
    · rw [head]
      exact xiVertexAncestorEdge_forward_none system coarse steps _
  change (_ ∨ _) at firstClass secondClass
  rcases firstClass with firstInterior | firstBoundary
  · rcases secondClass with secondInterior | secondBoundary
    · exact (distinct (Option.some.inj (firstInterior.symm.trans secondInterior))).elim
    · exact ((Option.some_ne_none _)
        (firstInterior.symm.trans (boundaryNone secondBoundary))).elim
  · refine ⟨firstBoundary, ?_⟩
    rcases secondClass with secondInterior | secondBoundary
    · exact ((Option.some_ne_none _)
        (secondInterior.symm.trans (boundaryNone firstBoundary))).elim
    · exact secondBoundary

end
end EIGS

#print axioms EIGS.xiVertexAncestorEdge_forward_none
#print axioms EIGS.xiDescendant_endpoints_coarseCellVertex
#print axioms EIGS.xiDistinctCoarseCells_common_endpoint_is_boundary
