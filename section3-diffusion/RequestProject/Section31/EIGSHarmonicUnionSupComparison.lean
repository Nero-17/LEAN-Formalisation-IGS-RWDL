import RequestProject.Section31.EIGSHarmonicFamilyCells
import RequestProject.Section31.EIGSHarmonicJointUniform

/-! Actual harmonic restrictions at absolute levels and their supremum
comparison. These finite-network and dense-completion arguments do not
assume continuity of arbitrary finite-energy skeleton functions.
Candidate source: compilation is not claimed. -/

namespace EIGS
open Filter Topology
open scoped BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 3000000
variable {K : ℕ}

section Harmonic
variable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)

theorem xiHarmonicUnionExtension_step (initialLevel level : ℕ)
    (initialValues : XiVtx system initialLevel → ℝ) (afterInitial : initialLevel ≤ level) :
    (fun vertex => xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair initialLevel initialValues
        (xiVertexEmbedding system (level + 1) vertex)) =
    xiHarmonicStep system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive eigenpair
      level (fun vertex => xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive
        resistanceVector vectorPositive eigenpair initialLevel initialValues (xiVertexEmbedding system level vertex)) := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le afterInitial
  have restriction : (fun vertex => xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair initialLevel initialValues
        (xiVertexEmbedding system (initialLevel + offset) vertex)) =
      xiHarmonicValues system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive eigenpair
        initialLevel initialValues offset := funext fun vertex =>
    xiHarmonicUnionExtension_values system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair initialLevel initialValues offset vertex
  rw [restriction]
  funext vertex
  exact xiHarmonicUnionExtension_values system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
    eigenpair initialLevel initialValues (offset + 1) vertex

theorem xiHarmonicFamily_abs_le (initialLevel : ℕ) (values : ∀ level, XiVtx system level → ℝ)
    (stepAgreement : ∀ level, initialLevel ≤ level → values (level + 1) =
      xiHarmonicStep system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive eigenpair
        level (values level))
    (bound : ℝ) (initialBound : ∀ vertex, |values initialLevel vertex| ≤ bound)
    (offset : ℕ) (vertex : XiVtx system (initialLevel + offset)) :
    |values (initialLevel + offset) vertex| ≤ bound := by
  obtain ⟨edge, incident⟩ := xiVertex_has_incident_edge system rulesConnected (initialLevel + offset) vertex
  have ranges := xiHarmonicFamily_descendant_range system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive eigenpair initialLevel values stepAgreement offset edge
  have tailBound := abs_le.mp (initialBound (XiTail system initialLevel (xiEdgeAncestor system initialLevel offset edge)))
  have headBound := abs_le.mp (initialBound (XiHead system initialLevel (xiEdgeAncestor system initialLevel offset edge)))
  have lower := le_min tailBound.1 headBound.1
  have upper := max_le tailBound.2 headBound.2
  apply abs_le.mpr
  rcases incident with tail | head
  · rw [← tail]
    exact ⟨lower.trans ranges.1.1, ranges.1.2.trans upper⟩
  · rw [← head]
    exact ⟨lower.trans ranges.2.1, ranges.2.2.trans upper⟩

theorem xiHarmonicUnionExtension_successor_sub_bound
    (level : ℕ) (values : XiVertexUnion system → ℝ) (bound : ℝ)
    (boundaryBound : ∀ vertex : XiVtx system (level + 1),
      |values (xiVertexEmbedding system (level + 1) vertex) -
        xiHarmonicStep system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive eigenpair
          level (values ∘ xiVertexEmbedding system level) vertex| ≤ bound) :
    ∀ vertex : XiVertexUnion system,
      |xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive eigenpair
          (level + 1) (values ∘ xiVertexEmbedding system (level + 1)) vertex -
        xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive eigenpair
          level (values ∘ xiVertexEmbedding system level) vertex| ≤ bound := by
  let family : ∀ fine, XiVtx system fine → ℝ := fun fine vertex =>
    xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive eigenpair
        (level + 1) (values ∘ xiVertexEmbedding system (level + 1)) (xiVertexEmbedding system fine vertex) -
      xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive eigenpair
        level (values ∘ xiVertexEmbedding system level) (xiVertexEmbedding system fine vertex)
  have familyStep : ∀ fine, level + 1 ≤ fine → family (fine + 1) =
      xiHarmonicStep system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive eigenpair
        fine (family fine) := by
    intro fine afterLevel
    have firstStep := xiHarmonicUnionExtension_step system rulesConnected resistanceRate ratePositive resistanceVector
      vectorPositive eigenpair (level + 1) fine (values ∘ xiVertexEmbedding system (level + 1)) afterLevel
    have secondStep := xiHarmonicUnionExtension_step system rulesConnected resistanceRate ratePositive resistanceVector
      vectorPositive eigenpair level fine (values ∘ xiVertexEmbedding system level) (by omega)
    dsimp only [family]
    change _ - _ = xiHarmonicStep system rulesConnected resistanceRate ratePositive resistanceVector
      vectorPositive eigenpair fine (_ - _)
    rw [firstStep, secondStep]
    simp only [← xiHarmonicStepLinearMap_apply, map_sub]
  have familyBoundary : ∀ vertex, |family (level + 1) vertex| ≤ bound := by
    intro vertex
    have first := xiHarmonicUnionExtension_values system rulesConnected resistanceRate ratePositive resistanceVector
      vectorPositive eigenpair (level + 1) (values ∘ xiVertexEmbedding system (level + 1)) 0 vertex
    have second := xiHarmonicUnionExtension_values system rulesConnected resistanceRate ratePositive resistanceVector
      vectorPositive eigenpair level (values ∘ xiVertexEmbedding system level) 1 vertex
    change _ = values (xiVertexEmbedding system (level + 1) vertex) at first
    change _ = xiHarmonicStep system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive eigenpair
      level (values ∘ xiVertexEmbedding system level) vertex at second
    dsimp only [family]
    rw [first, second]
    exact boundaryBound vertex
  intro vertex
  obtain ⟨offset, finiteVertex, rfl⟩ := xiVertexUnion_exhausted_after system (level + 1) vertex
  exact xiHarmonicFamily_abs_le system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
    eigenpair (level + 1) family familyStep bound familyBoundary offset finiteVertex

end Harmonic
end
end EIGS

#print axioms EIGS.xiHarmonicUnionExtension_step
#print axioms EIGS.xiHarmonicFamily_abs_le
#print axioms EIGS.xiHarmonicUnionExtension_successor_sub_bound
