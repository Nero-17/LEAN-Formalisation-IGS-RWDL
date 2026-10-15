import RequestProject.Section31.EIGSUVFlowerRuleGeometry
import RequestProject.Section31.EIGSUVFlowerUnitFlow

/-! Explicit walks along both literal paths certify connectivity of
the genuine unequal-path flower. The path-point definition is shared
with the actual electrical certificate. -/

namespace EIGS
noncomputable section
open scoped Classical

@[simp] theorem uvFlowerPathPoint_height (length : ℕ) (position : Fin (length + 1)) :
    uvFlowerPathHeight length (uvFlowerPathPoint length position) = position.val := by
  unfold uvFlowerPathPoint
  split_ifs with first last
  · simp [uvFlowerPathHeight, first]
  · simp [uvFlowerPathHeight, last]
  · simp only [uvFlowerPathHeight]
    omega

theorem uvFlowerRuleGraph_left_edge_adj (firstLength secondLength : ℕ) (edge : Fin firstLength) :
    (ruleSG (uvFlowerSystem firstLength secondLength) 0).Adj
      (uvFlowerLeftEmbedding firstLength secondLength (uvFlowerPathTail firstLength edge))
      (uvFlowerLeftEmbedding firstLength secondLength (uvFlowerPathHead firstLength edge)) := by
  have distinct : uvFlowerLeftEmbedding firstLength secondLength (uvFlowerPathTail firstLength edge) ≠
      uvFlowerLeftEmbedding firstLength secondLength (uvFlowerPathHead firstLength edge) := by
    intro equality
    have heights := congrArg (fun vertex => uvFlowerPathHeight firstLength
      (uvFlowerLeftProjection firstLength secondLength vertex)) equality
    simp only [uvFlowerLeftProjection_embedding, uvFlowerPathTail_height, uvFlowerPathHead_height] at heights
    omega
  change _ ≠ _ ∧ ((∃ other : UVFlowerEdge firstLength secondLength,
    (uvFlowerRuleGraph firstLength secondLength).tail other = _ ∧
      (uvFlowerRuleGraph firstLength secondLength).head other = _) ∨
    (∃ other : UVFlowerEdge firstLength secondLength,
    (uvFlowerRuleGraph firstLength secondLength).tail other = _ ∧
      (uvFlowerRuleGraph firstLength secondLength).head other = _))
  exact ⟨distinct, Or.inr ⟨Sum.inl edge, rfl, rfl⟩⟩

theorem uvFlowerRuleGraph_right_edge_adj (firstLength secondLength : ℕ) (edge : Fin secondLength) :
    (ruleSG (uvFlowerSystem firstLength secondLength) 0).Adj
      (uvFlowerRightEmbedding firstLength secondLength (uvFlowerPathTail secondLength edge))
      (uvFlowerRightEmbedding firstLength secondLength (uvFlowerPathHead secondLength edge)) := by
  have distinct : uvFlowerRightEmbedding firstLength secondLength (uvFlowerPathTail secondLength edge) ≠
      uvFlowerRightEmbedding firstLength secondLength (uvFlowerPathHead secondLength edge) := by
    intro equality
    have heights := congrArg (fun vertex => uvFlowerPathHeight secondLength
      (uvFlowerRightProjection firstLength secondLength vertex)) equality
    simp only [uvFlowerRightProjection_embedding, uvFlowerPathTail_height, uvFlowerPathHead_height] at heights
    omega
  change _ ≠ _ ∧ ((∃ other : UVFlowerEdge firstLength secondLength,
    (uvFlowerRuleGraph firstLength secondLength).tail other = _ ∧
      (uvFlowerRuleGraph firstLength secondLength).head other = _) ∨
    (∃ other : UVFlowerEdge firstLength secondLength,
    (uvFlowerRuleGraph firstLength secondLength).tail other = _ ∧
      (uvFlowerRuleGraph firstLength secondLength).head other = _))
  exact ⟨distinct, Or.inl ⟨Sum.inr edge, rfl, rfl⟩⟩

theorem uvFlowerLeftPoint_reachable (firstLength secondLength : ℕ)
    (position : Fin (firstLength + 1)) :
    (ruleSG (uvFlowerSystem firstLength secondLength) 0).Reachable (Sum.inl false)
      (uvFlowerLeftEmbedding firstLength secondLength (uvFlowerPathPoint firstLength position)) := by
  have reaches : ∀ index : ℕ, (bound : index ≤ firstLength) →
      (ruleSG (uvFlowerSystem firstLength secondLength) 0).Reachable (Sum.inl false)
        (uvFlowerLeftEmbedding firstLength secondLength
          (uvFlowerPathPoint firstLength ⟨index, by omega⟩)) := by
    intro index
    induction index with
    | zero =>
      intro bound
      simpa [uvFlowerPathPoint, uvFlowerLeftEmbedding] using
        (SimpleGraph.Reachable.refl (G := ruleSG (uvFlowerSystem firstLength secondLength) 0) (Sum.inl false))
    | succ index induction =>
      intro bound
      let edge : Fin firstLength := ⟨index, by omega⟩
      have adjacent := uvFlowerRuleGraph_left_edge_adj firstLength secondLength edge
      have joined : (ruleSG (uvFlowerSystem firstLength secondLength) 0).Reachable
          (uvFlowerLeftEmbedding firstLength secondLength
            (uvFlowerPathPoint firstLength ⟨index, by omega⟩))
          (uvFlowerLeftEmbedding firstLength secondLength
            (uvFlowerPathPoint firstLength ⟨index + 1, by omega⟩)) := by
        simpa only [uvFlowerPathTail_eq_point, uvFlowerPathHead_eq_point] using adjacent.reachable
      exact (induction (by omega)).trans joined
  exact reaches position.val (by omega)

theorem uvFlowerRightPoint_reachable (firstLength secondLength : ℕ)
    (position : Fin (secondLength + 1)) :
    (ruleSG (uvFlowerSystem firstLength secondLength) 0).Reachable (Sum.inl false)
      (uvFlowerRightEmbedding firstLength secondLength (uvFlowerPathPoint secondLength position)) := by
  have reaches : ∀ index : ℕ, (bound : index ≤ secondLength) →
      (ruleSG (uvFlowerSystem firstLength secondLength) 0).Reachable (Sum.inl false)
        (uvFlowerRightEmbedding firstLength secondLength
          (uvFlowerPathPoint secondLength ⟨index, by omega⟩)) := by
    intro index
    induction index with
    | zero =>
      intro bound
      simpa [uvFlowerPathPoint, uvFlowerRightEmbedding] using
        (SimpleGraph.Reachable.refl (G := ruleSG (uvFlowerSystem firstLength secondLength) 0) (Sum.inl false))
    | succ index induction =>
      intro bound
      let edge : Fin secondLength := ⟨index, by omega⟩
      have adjacent := uvFlowerRuleGraph_right_edge_adj firstLength secondLength edge
      have joined : (ruleSG (uvFlowerSystem firstLength secondLength) 0).Reachable
          (uvFlowerRightEmbedding firstLength secondLength
            (uvFlowerPathPoint secondLength ⟨index, by omega⟩))
          (uvFlowerRightEmbedding firstLength secondLength
            (uvFlowerPathPoint secondLength ⟨index + 1, by omega⟩)) := by
        simpa only [uvFlowerPathTail_eq_point, uvFlowerPathHead_eq_point] using adjacent.reachable
      exact (induction (by omega)).trans joined
  exact reaches position.val (by omega)

theorem uvFlowerSystem_connected (firstLength secondLength : ℕ)
    (firstPositive : 0 < firstLength) (secondPositive : 0 < secondLength) (colour : Fin 1) :
    (ruleSG (uvFlowerSystem firstLength secondLength) colour).Connected := by
  have colourZero : colour = 0 := Subsingleton.elim _ _
  subst colour
  letI : Nonempty ((uvFlowerSystem firstLength secondLength).rule 0).V := ⟨Sum.inl false⟩
  have reaches (vertex : UVFlowerVertex firstLength secondLength) :
      (ruleSG (uvFlowerSystem firstLength secondLength) 0).Reachable (Sum.inl false) vertex := by
    cases vertex with
    | inl endpoint =>
      cases endpoint with
      | false => exact SimpleGraph.Reachable.refl _
      | true =>
        have toSink := uvFlowerLeftPoint_reachable firstLength secondLength ⟨firstLength, by omega⟩
        simpa [uvFlowerPathPoint, uvFlowerLeftEmbedding, Nat.ne_of_gt firstPositive] using toSink
    | inr interior =>
      cases interior with
      | inl interior =>
        have toInterior := uvFlowerLeftPoint_reachable firstLength secondLength ⟨interior.val + 1, by omega⟩
        have beforeSink : interior.val + 1 ≠ firstLength := by omega
        simpa [uvFlowerPathPoint, uvFlowerLeftEmbedding, beforeSink] using toInterior
      | inr interior =>
        have toInterior := uvFlowerRightPoint_reachable firstLength secondLength ⟨interior.val + 1, by omega⟩
        have beforeSink : interior.val + 1 ≠ secondLength := by omega
        simpa [uvFlowerPathPoint, uvFlowerRightEmbedding, beforeSink] using toInterior
  exact ⟨fun first second => (reaches first).symm.trans (reaches second)⟩

theorem uvFlowerSystem_distancePositive (firstLength secondLength : ℕ) (ruleColour edgeColour : Fin 1) :
    ¬ (((uvFlowerSystem firstLength secondLength).ruleNetwork ruleColour).withoutColour edgeColour).Reachable
      ((uvFlowerSystem firstLength secondLength).plantPlus ruleColour)
      ((uvFlowerSystem firstLength secondLength).plantMinus ruleColour) := by
  have edgeZero : edgeColour = 0 := Subsingleton.elim _ _
  subst edgeColour
  have graphEmpty : (((uvFlowerSystem firstLength secondLength).ruleNetwork ruleColour).withoutColour 0) = ⊥ := by
    ext first second
    simp [Network.withoutColour, EIGSData.ruleNetwork]
  rw [graphEmpty, SimpleGraph.reachable_bot]
  exact (uvFlowerSystem firstLength secondLength).plant_ne ruleColour

end
end EIGS

#print axioms EIGS.uvFlowerPathPoint_height
#print axioms EIGS.uvFlowerLeftPoint_reachable
#print axioms EIGS.uvFlowerRightPoint_reachable
#print axioms EIGS.uvFlowerSystem_connected
#print axioms EIGS.uvFlowerSystem_distancePositive
