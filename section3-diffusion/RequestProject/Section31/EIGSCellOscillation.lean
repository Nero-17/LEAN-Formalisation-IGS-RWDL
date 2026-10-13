import RequestProject.Section31.EIGSCellConvexity

/-! Actual descendant cells are defined by the unchanged sigma edge genealogy.
Every harmonic value in such a cell stays in the ancestor endpoint interval.
This is a statement on the constructed vertex union, before metric completion. -/

namespace EIGS

variable {K : ℕ}

def xiDescendantCellVertices (system : EIGSData K) (initialLevel : ℕ)
    (ancestor : XiEdge system.toRuleData initialLevel) : Set (XiVertexUnion system) :=
  {vertex | ∃ offset, ∃ edge : XiEdge system.toRuleData (initialLevel + offset),
    xiAncestorEdge system initialLevel offset edge = ancestor ∧
      (xiVertexEmbedding system (initialLevel + offset) (XiTail system (initialLevel + offset) edge) = vertex ∨
       xiVertexEmbedding system (initialLevel + offset) (XiHead system (initialLevel + offset) edge) = vertex)}

section Eigenpair

variable (system : EIGSData K)
  (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
  (resistanceRate : ℝ) (resistanceRatePositive : 0 < resistanceRate)
  (resistanceVector : Fin K → ℝ)
  (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour)
  (renormalizationEigenpair : ∀ colour,
    (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)

theorem xiHarmonicValues_descendant_endpoint_range
    (initialLevel : ℕ) (initialValues : XiVtx system initialLevel → ℝ) :
    ∀ offset (edge : XiEdge system.toRuleData (initialLevel + offset)),
      (min (initialValues (XiTail system initialLevel (xiAncestorEdge system initialLevel offset edge)))
          (initialValues (XiHead system initialLevel (xiAncestorEdge system initialLevel offset edge))) ≤
        xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset
            (XiTail system (initialLevel + offset) edge) ∧
       xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset
            (XiTail system (initialLevel + offset) edge) ≤
        max (initialValues (XiTail system initialLevel (xiAncestorEdge system initialLevel offset edge)))
          (initialValues (XiHead system initialLevel (xiAncestorEdge system initialLevel offset edge)))) ∧
      (min (initialValues (XiTail system initialLevel (xiAncestorEdge system initialLevel offset edge)))
          (initialValues (XiHead system initialLevel (xiAncestorEdge system initialLevel offset edge))) ≤
        xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset
            (XiHead system (initialLevel + offset) edge) ∧
       xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset
            (XiHead system (initialLevel + offset) edge) ≤
        max (initialValues (XiTail system initialLevel (xiAncestorEdge system initialLevel offset edge)))
          (initialValues (XiHead system initialLevel (xiAncestorEdge system initialLevel offset edge)))) := by
  intro offset
  induction offset with
  | zero =>
      intro edge
      exact ⟨⟨min_le_left _ _, le_max_left _ _⟩, ⟨min_le_right _ _, le_max_right _ _⟩⟩
  | succ offset induction =>
      intro edge
      have parentRange := induction edge.1
      have tailRange := xiHarmonicStep_rule_vertex_range system rulesConnected resistanceRate
        resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair
          (initialLevel + offset)
          (xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
            resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset)
          edge.1 ((system.rule _).tail edge.2)
      have headRange := xiHarmonicStep_rule_vertex_range system rulesConnected resistanceRate
        resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair
          (initialLevel + offset)
          (xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
            resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset)
          edge.1 ((system.rule _).head edge.2)
      exact ⟨⟨(le_min parentRange.1.1 parentRange.2.1).trans tailRange.1,
          tailRange.2.trans (max_le parentRange.1.2 parentRange.2.2)⟩,
        ⟨(le_min parentRange.1.1 parentRange.2.1).trans headRange.1,
          headRange.2.trans (max_le parentRange.1.2 parentRange.2.2)⟩⟩

theorem xiHarmonic_union_cell_range
    (initialLevel : ℕ) (initialValues : XiVtx system initialLevel → ℝ)
    (extension : XiVertexUnion system → ℝ)
    (extensionValues : ∀ offset (vertex : XiVtx system (initialLevel + offset)),
      extension (xiVertexEmbedding system (initialLevel + offset) vertex) =
        xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset vertex)
    (ancestor : XiEdge system.toRuleData initialLevel)
    (vertex : XiVertexUnion system)
    (membership : vertex ∈ xiDescendantCellVertices system initialLevel ancestor) :
    min (initialValues (XiTail system initialLevel ancestor))
        (initialValues (XiHead system initialLevel ancestor)) ≤ extension vertex ∧
      extension vertex ≤ max (initialValues (XiTail system initialLevel ancestor))
        (initialValues (XiHead system initialLevel ancestor)) := by
  obtain ⟨offset, edge, ancestorEquality, endpointEquality⟩ := membership
  have endpointRange := xiHarmonicValues_descendant_endpoint_range system rulesConnected resistanceRate
    resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair
      initialLevel initialValues offset edge
  rw [ancestorEquality] at endpointRange
  rcases endpointEquality with tailEquality | headEquality
  · rw [← tailEquality, extensionValues]
    exact endpointRange.1
  · rw [← headEquality, extensionValues]
    exact endpointRange.2

private theorem abs_sub_le_endpoint_difference (first second left right : ℝ)
    (leftRange : min first second ≤ left ∧ left ≤ max first second)
    (rightRange : min first second ≤ right ∧ right ≤ max first second) :
    |left - right| ≤ |first - second| := by
  by_cases endpointsOrdered : first ≤ second
  · rw [min_eq_left endpointsOrdered, max_eq_right endpointsOrdered] at leftRange rightRange
    rw [abs_of_nonpos (sub_nonpos.2 endpointsOrdered)]
    exact abs_le.2 ⟨by linarith [leftRange.1, rightRange.2],
      by linarith [leftRange.2, rightRange.1]⟩
  · have reverseOrder : second ≤ first := le_of_not_ge endpointsOrdered
    rw [min_eq_right reverseOrder, max_eq_left reverseOrder] at leftRange rightRange
    rw [abs_of_nonneg (sub_nonneg.2 reverseOrder)]
    exact abs_le.2 ⟨by linarith [leftRange.1, rightRange.2],
      by linarith [leftRange.2, rightRange.1]⟩

theorem xiHarmonic_union_cell_oscillation
    (initialLevel : ℕ) (initialValues : XiVtx system initialLevel → ℝ)
    (extension : XiVertexUnion system → ℝ)
    (extensionValues : ∀ offset (vertex : XiVtx system (initialLevel + offset)),
      extension (xiVertexEmbedding system (initialLevel + offset) vertex) =
        xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset vertex)
    (ancestor : XiEdge system.toRuleData initialLevel)
    (left right : XiVertexUnion system)
    (leftMembership : left ∈ xiDescendantCellVertices system initialLevel ancestor)
    (rightMembership : right ∈ xiDescendantCellVertices system initialLevel ancestor) :
    |extension left - extension right| ≤
      |initialValues (XiTail system initialLevel ancestor) - initialValues (XiHead system initialLevel ancestor)| := by
  exact abs_sub_le_endpoint_difference _ _ _ _
    (xiHarmonic_union_cell_range system rulesConnected resistanceRate resistanceRatePositive resistanceVector
      resistanceVectorPositive renormalizationEigenpair initialLevel initialValues extension extensionValues
        ancestor left leftMembership)
    (xiHarmonic_union_cell_range system rulesConnected resistanceRate resistanceRatePositive resistanceVector
      resistanceVectorPositive renormalizationEigenpair initialLevel initialValues extension extensionValues
        ancestor right rightMembership)

end Eigenpair

end EIGS
