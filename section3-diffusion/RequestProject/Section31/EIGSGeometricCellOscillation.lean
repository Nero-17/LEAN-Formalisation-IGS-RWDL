import RequestProject.Section31.EIGSCellOscillation
import RequestProject.Section31.EIGSHarmonicDecay

/-! Geometric oscillation on actual descendant cells. No metric mesh estimate
or completed-space continuity is a premise or a conclusion here. -/

namespace EIGS

variable {K : ℕ}

section Eigenpair

variable (system : EIGSData K)
  (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
  (resistanceRate : ℝ) (resistanceRatePositive : 0 < resistanceRate)
  (resistanceVector : Fin K → ℝ)
  (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour)
  (renormalizationEigenpair : ∀ colour,
    (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)

theorem xiUnion_values_eq_harmonicValues_of_steps
    (initialLevel : ℕ) (extension : XiVertexUnion system → ℝ)
    (extensionSteps : ∀ level, initialLevel ≤ level → ∀ vertex : XiVtx system (level + 1),
      extension (xiVertexEmbedding system (level + 1) vertex) =
        xiHarmonicStep system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair level
            (extension ∘ xiVertexEmbedding system level) vertex) :
    ∀ offset (vertex : XiVtx system (initialLevel + offset)),
      extension (xiVertexEmbedding system (initialLevel + offset) vertex) =
        xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair initialLevel
            (extension ∘ xiVertexEmbedding system initialLevel) offset vertex := by
  intro offset
  induction offset with
  | zero => intro vertex; rfl
  | succ offset induction =>
      intro vertex
      change extension (xiVertexEmbedding system ((initialLevel + offset) + 1) vertex) =
        xiHarmonicStep system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair (initialLevel + offset)
            (xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
              resistanceVectorPositive renormalizationEigenpair initialLevel
                (extension ∘ xiVertexEmbedding system initialLevel) offset) vertex
      rw [extensionSteps (initialLevel + offset) (Nat.le_add_right _ _) vertex]
      rw [show extension ∘ xiVertexEmbedding system (initialLevel + offset) =
        xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair initialLevel
            (extension ∘ xiVertexEmbedding system initialLevel) offset from funext induction]

theorem xiHarmonic_union_steps
    (initialLevel : ℕ) (initialValues : XiVtx system initialLevel → ℝ)
    (extension : XiVertexUnion system → ℝ)
    (extensionValues : ∀ offset (vertex : XiVtx system (initialLevel + offset)),
      extension (xiVertexEmbedding system (initialLevel + offset) vertex) =
        xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset vertex) :
    ∀ level, initialLevel ≤ level → ∀ vertex : XiVtx system (level + 1),
      extension (xiVertexEmbedding system (level + 1) vertex) =
        xiHarmonicStep system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair level
            (extension ∘ xiVertexEmbedding system level) vertex := by
  intro level afterInitial vertex
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le afterInitial
  rw [show extension ∘ xiVertexEmbedding system (initialLevel + offset) =
    xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
      resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset from
        funext (extensionValues offset)]
  exact extensionValues (offset + 1) vertex

theorem xiUnion_cell_oscillation_of_steps
    (initialLevel : ℕ) (extension : XiVertexUnion system → ℝ)
    (extensionSteps : ∀ level, initialLevel ≤ level → ∀ vertex : XiVtx system (level + 1),
      extension (xiVertexEmbedding system (level + 1) vertex) =
        xiHarmonicStep system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair level
            (extension ∘ xiVertexEmbedding system level) vertex)
    (cellLevel : ℕ) (afterInitial : initialLevel ≤ cellLevel)
    (ancestor : XiEdge system.toRuleData cellLevel)
    (left right : XiVertexUnion system)
    (leftMembership : left ∈ xiDescendantCellVertices system cellLevel ancestor)
    (rightMembership : right ∈ xiDescendantCellVertices system cellLevel ancestor) :
    |extension left - extension right| ≤
      |extension (xiVertexEmbedding system cellLevel (XiTail system cellLevel ancestor)) -
        extension (xiVertexEmbedding system cellLevel (XiHead system cellLevel ancestor))| := by
  apply xiHarmonic_union_cell_oscillation system rulesConnected resistanceRate resistanceRatePositive
    resistanceVector resistanceVectorPositive renormalizationEigenpair cellLevel
      (extension ∘ xiVertexEmbedding system cellLevel) extension _ ancestor left right
        leftMembership rightMembership
  exact xiUnion_values_eq_harmonicValues_of_steps system rulesConnected resistanceRate resistanceRatePositive
    resistanceVector resistanceVectorPositive renormalizationEigenpair cellLevel extension
      (fun level afterCell => extensionSteps level (afterInitial.trans afterCell))

end Eigenpair

theorem exists_xiHarmonic_geometric_cell_oscillation (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour)) :
    ∃ resistanceRate : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ resistanceRatePositive : 0 < resistanceRate,
      ∃ resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour =
          resistanceRate * resistanceVector colour,
      ∃ contractionFactor : ℝ, 0 < contractionFactor ∧ contractionFactor < 1 ∧
        ∀ initialLevel (initialValues : XiVtx system initialLevel → ℝ) (initialBound : ℝ),
          (∀ edge : XiEdge system.toRuleData initialLevel,
            |initialValues (XiTail system initialLevel edge) - initialValues (XiHead system initialLevel edge)| ≤ initialBound) →
          ∃ extension : XiVertexUnion system → ℝ,
            (∀ offset (vertex : XiVtx system (initialLevel + offset)),
              extension (xiVertexEmbedding system (initialLevel + offset) vertex) =
                xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
                  resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset vertex) ∧
            xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive resistanceVector
              resistanceVectorPositive extension = ENNReal.ofReal
                ((xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector
                  resistanceVectorPositive initialLevel).energy initialValues) ∧
            ∀ offset (ancestor : XiEdge system.toRuleData (initialLevel + offset))
              (left right : XiVertexUnion system),
              left ∈ xiDescendantCellVertices system (initialLevel + offset) ancestor →
              right ∈ xiDescendantCellVertices system (initialLevel + offset) ancestor →
              |extension left - extension right| ≤ contractionFactor ^ offset * initialBound := by
  obtain ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, coordinateEigenpair,
      contractionFactor, factorPositive, factorStrict, edgeDecay⟩ :=
    exists_xiHarmonic_geometric_edge_decay system rulesConnected distancePositive oneColourDistance
  refine ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, coordinateEigenpair,
    contractionFactor, factorPositive, factorStrict, ?_⟩
  intro initialLevel initialValues initialBound initialEdgeBound
  obtain ⟨extension, extensionValues, extensionEnergy⟩ := exists_xiHarmonic_union_extension system
    rulesConnected resistanceRate ratePositive resistanceVector vectorPositive coordinateEigenpair
      initialLevel initialValues
  refine ⟨extension, extensionValues, extensionEnergy, ?_⟩
  intro offset ancestor left right leftMembership rightMembership
  have extensionSteps := xiHarmonic_union_steps system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive coordinateEigenpair initialLevel initialValues extension extensionValues
  have cellBound := xiUnion_cell_oscillation_of_steps system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive coordinateEigenpair initialLevel extension extensionSteps
      (initialLevel + offset) (Nat.le_add_right _ _) ancestor left right leftMembership rightMembership
  rw [extensionValues offset, extensionValues offset] at cellBound
  exact cellBound.trans (edgeDecay initialLevel initialValues initialBound initialEdgeBound offset ancestor)

end EIGS
