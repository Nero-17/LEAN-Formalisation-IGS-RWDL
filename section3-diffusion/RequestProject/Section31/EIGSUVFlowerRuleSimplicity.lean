import RequestProject.Section31.EIGSUVFlowerRuleGeometry

/-! The genuine two-path flower has unique undirected edges when both
paths have at least two edges. An interior endpoint determines its path,
and the smaller path height determines the edge within that path. -/

namespace EIGS
noncomputable section
open scoped Classical

theorem uvFlowerRuleGraph_minimum_left_height (firstLength secondLength : ℕ)
    (edge : Fin firstLength) :
    min (uvFlowerPathHeight firstLength (uvFlowerLeftProjection firstLength secondLength
        ((uvFlowerRuleGraph firstLength secondLength).tail (Sum.inl edge))))
      (uvFlowerPathHeight firstLength (uvFlowerLeftProjection firstLength secondLength
        ((uvFlowerRuleGraph firstLength secondLength).head (Sum.inl edge)))) = edge.val := by
  simp only [uvFlowerRuleGraph, Sum.elim_inl, uvFlowerLeftProjection_embedding,
    uvFlowerPathTail_height, uvFlowerPathHead_height]
  omega

theorem uvFlowerRuleGraph_minimum_right_height (firstLength secondLength : ℕ)
    (edge : Fin secondLength) :
    min (uvFlowerPathHeight secondLength (uvFlowerRightProjection firstLength secondLength
        ((uvFlowerRuleGraph firstLength secondLength).tail (Sum.inr edge))))
      (uvFlowerPathHeight secondLength (uvFlowerRightProjection firstLength secondLength
        ((uvFlowerRuleGraph firstLength secondLength).head (Sum.inr edge)))) = edge.val := by
  simp only [uvFlowerRuleGraph, Sum.elim_inr, uvFlowerRightProjection_embedding,
    uvFlowerPathTail_height, uvFlowerPathHead_height]
  omega

theorem uvFlowerSystem_edgesUnique (firstLength secondLength : ℕ)
    (firstAtLeastTwo : 2 ≤ firstLength) (secondAtLeastTwo : 2 ≤ secondLength) (colour : Fin 1) :
    ((uvFlowerSystem firstLength secondLength).ruleNetwork colour).EdgesUnique := by
  intro first second endpoints
  change (((uvFlowerRuleGraph firstLength secondLength).tail first =
        (uvFlowerRuleGraph firstLength secondLength).tail second ∧
      (uvFlowerRuleGraph firstLength secondLength).head first =
        (uvFlowerRuleGraph firstLength secondLength).head second) ∨
    ((uvFlowerRuleGraph firstLength secondLength).tail first =
        (uvFlowerRuleGraph firstLength secondLength).head second ∧
      (uvFlowerRuleGraph firstLength secondLength).head first =
        (uvFlowerRuleGraph firstLength secondLength).tail second)) at endpoints
  have branchEquality : uvFlowerEdgeBranch firstLength secondLength first =
      uvFlowerEdgeBranch firstLength secondLength second := by
    have supported := uvFlowerRuleGraph_has_labeled_endpoint firstLength secondLength
      firstAtLeastTwo secondAtLeastTwo first
    have secondLabels := uvFlowerRuleGraph_endpoint_labels firstLength secondLength second
    have determine (label : Option Bool)
        (secondLabel : label = none ∨ label = some (uvFlowerEdgeBranch firstLength secondLength second))
        (firstLabel : label = some (uvFlowerEdgeBranch firstLength secondLength first)) :
        uvFlowerEdgeBranch firstLength secondLength first = uvFlowerEdgeBranch firstLength secondLength second := by
      rcases secondLabel with absent | present
      · rw [absent] at firstLabel
        cases firstLabel
      · exact Option.some.inj (firstLabel.symm.trans present)
    rcases endpoints with ⟨tail, head⟩ | ⟨tail, head⟩
    · rw [tail, head] at supported
      exact supported.elim (determine _ secondLabels.1) (determine _ secondLabels.2)
    · rw [tail, head] at supported
      exact supported.elim (determine _ secondLabels.2) (determine _ secondLabels.1)
  have minimumEquality (height : UVFlowerVertex firstLength secondLength → ℕ) :
      min (height ((uvFlowerRuleGraph firstLength secondLength).tail first))
          (height ((uvFlowerRuleGraph firstLength secondLength).head first)) =
        min (height ((uvFlowerRuleGraph firstLength secondLength).tail second))
          (height ((uvFlowerRuleGraph firstLength secondLength).head second)) := by
    rcases endpoints with ⟨tail, head⟩ | ⟨tail, head⟩
    · exact congrArg₂ min (congrArg height tail) (congrArg height head)
    · rw [tail, head]
      exact min_comm _ _
  cases first with
  | inl first =>
    cases second with
    | inl second =>
      have heights := minimumEquality (fun vertex => uvFlowerPathHeight firstLength
        (uvFlowerLeftProjection firstLength secondLength vertex))
      rw [uvFlowerRuleGraph_minimum_left_height, uvFlowerRuleGraph_minimum_left_height] at heights
      exact congrArg Sum.inl (Fin.ext heights)
    | inr second => simp [uvFlowerEdgeBranch] at branchEquality
  | inr first =>
    cases second with
    | inl second => simp [uvFlowerEdgeBranch] at branchEquality
    | inr second =>
      have heights := minimumEquality (fun vertex => uvFlowerPathHeight secondLength
        (uvFlowerRightProjection firstLength secondLength vertex))
      rw [uvFlowerRuleGraph_minimum_right_height, uvFlowerRuleGraph_minimum_right_height] at heights
      exact congrArg Sum.inr (Fin.ext heights)

theorem uvFlowerSystem_plantingNonadjacent (firstLength secondLength : ℕ)
    (firstAtLeastTwo : 2 ≤ firstLength) (secondAtLeastTwo : 2 ≤ secondLength) (colour : Fin 1) :
    ¬ (ruleSG (uvFlowerSystem firstLength secondLength) colour).Adj
      ((uvFlowerSystem firstLength secondLength).plantPlus colour)
      ((uvFlowerSystem firstLength secondLength).plantMinus colour) := by
  intro adjacent
  change (Sum.inl false ≠ Sum.inl true) ∧
    ((∃ edge : UVFlowerEdge firstLength secondLength,
      (uvFlowerRuleGraph firstLength secondLength).tail edge = Sum.inl false ∧
        (uvFlowerRuleGraph firstLength secondLength).head edge = Sum.inl true) ∨
    (∃ edge : UVFlowerEdge firstLength secondLength,
      (uvFlowerRuleGraph firstLength secondLength).tail edge = Sum.inl true ∧
        (uvFlowerRuleGraph firstLength secondLength).head edge = Sum.inl false)) at adjacent
  rcases adjacent.2 with ⟨edge, tail, head⟩ | ⟨edge, tail, head⟩ <;>
    cases edge with
    | inl edge =>
      have tailHeight := congrArg (fun vertex => uvFlowerPathHeight firstLength
        (uvFlowerLeftProjection firstLength secondLength vertex)) tail
      have headHeight := congrArg (fun vertex => uvFlowerPathHeight firstLength
        (uvFlowerLeftProjection firstLength secondLength vertex)) head
      simp only [uvFlowerRuleGraph, Sum.elim_inl, uvFlowerLeftProjection_embedding,
        uvFlowerPathTail_height, uvFlowerPathHead_height] at tailHeight headHeight
      simp only [uvFlowerLeftProjection, uvFlowerPathHeight] at tailHeight headHeight
      omega
    | inr edge =>
      have tailHeight := congrArg (fun vertex => uvFlowerPathHeight secondLength
        (uvFlowerRightProjection firstLength secondLength vertex)) tail
      have headHeight := congrArg (fun vertex => uvFlowerPathHeight secondLength
        (uvFlowerRightProjection firstLength secondLength vertex)) head
      simp only [uvFlowerRuleGraph, Sum.elim_inr, uvFlowerRightProjection_embedding,
        uvFlowerPathTail_height, uvFlowerPathHead_height] at tailHeight headHeight
      simp only [uvFlowerRightProjection, uvFlowerPathHeight] at tailHeight headHeight
      omega

end
end EIGS

#print axioms EIGS.uvFlowerRuleGraph_minimum_left_height
#print axioms EIGS.uvFlowerRuleGraph_minimum_right_height
#print axioms EIGS.uvFlowerSystem_edgesUnique
#print axioms EIGS.uvFlowerSystem_plantingNonadjacent
