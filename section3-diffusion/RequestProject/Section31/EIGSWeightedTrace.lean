import RequestProject.Section2Concrete
import RequestProject.Section31.EIGSTraceEnergy
import RequestProject.Section31.SubstitutionTrace
import RequestProject.Section31.TraceQuadraticForm

/-!
# Actual weighted trace compatibility

The finite trace minimum is specialized to the canonical EIGS substitution.
The positive eigenpair is first allowed as a parameter, then constructed from
connected distance-positive original rule graphs. The resulting energy
monotonicity is on the actual common vertex union.
-/

namespace EIGS

open IGS.Sec31

variable {K : ℕ}

theorem xiWeightedFiniteNetwork_energy_eq_potential (system : EIGSData K)
    (resistanceRate : ℝ) (resistanceRatePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ)
    (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour)
    (level : ℕ) (values : XiVtx system level → ℝ) :
    (xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector
      resistanceVectorPositive level).energy values =
      resistanceRate ^ level *
        ((XiNetwork system level).potentialNetwork resistanceVector resistanceVectorPositive).energy values := by
  simp only [FiniteNetwork.energy, xiWeightedFiniteNetwork, Network.potentialNetwork,
    XiNetwork, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro edge _
  simp only [XiTail, XiHead]
  ring

theorem xiPotentialEnergy_succ_eq_substituted (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceVector : Fin K → ℝ)
    (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour)
    (level : ℕ) (values : XiVtx system (level + 1) → ℝ) :
    ((XiNetwork system (level + 1)).potentialNetwork resistanceVector resistanceVectorPositive).energy values =
      (((XiNetwork system level).subst (system.ruleFamily rulesConnected)).potentialNetwork
        resistanceVector resistanceVectorPositive).energy values := rfl

/-- The attained trace minimum on the actual canonical EIGS successor graph. -/
theorem exists_xiWeighted_trace_of_eigenpair (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate : ℝ) (resistanceRatePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ)
    (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour =
        resistanceRate * resistanceVector colour)
    (level : ℕ) (oldValues : XiVtx system level → ℝ) :
    ∃ extension : XiVtx system (level + 1) → ℝ,
      (∀ vertex, extension (Sum.inl vertex) = oldValues vertex) ∧
      (xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive (level + 1)).energy extension =
        (xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive level).energy oldValues ∧
      (∀ competitor : XiVtx system (level + 1) → ℝ,
        (∀ vertex, competitor (Sum.inl vertex) = oldValues vertex) →
        (xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive level).energy oldValues ≤
          (xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector
            resistanceVectorPositive (level + 1)).energy competitor) := by
  obtain ⟨extension, extensionOld, scaledEnergy, lowerBound⟩ :=
    (XiNetwork system level).exists_substituted_eigenvector_trace (system.ruleFamily rulesConnected)
      resistanceVector resistanceVectorPositive rulesConnected resistanceRate resistanceRatePositive
      renormalizationEigenpair oldValues
  refine ⟨extension, extensionOld, ?_, ?_⟩
  · rw [xiWeightedFiniteNetwork_energy_eq_potential,
      xiPotentialEnergy_succ_eq_substituted system rulesConnected,
      xiWeightedFiniteNetwork_energy_eq_potential, pow_succ, mul_assoc, scaledEnergy]
  · intro competitor competitorOld
    have scaledLower := mul_le_mul_of_nonneg_left (lowerBound competitor competitorOld)
      (pow_pos resistanceRatePositive level).le
    simpa only [xiWeightedFiniteNetwork_energy_eq_potential,
      xiPotentialEnergy_succ_eq_substituted system rulesConnected, pow_succ, mul_assoc] using scaledLower

theorem xiUnionWeightedNetwork_energy_increasing_of_eigenpair (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate : ℝ) (resistanceRatePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ)
    (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour =
        resistanceRate * resistanceVector colour) :
    ∀ values : XiVertexUnion system → ℝ,
      Monotone (fun level =>
        (xiUnionWeightedNetwork system resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive level).energy values) := by
  intro values
  apply monotone_nat_of_le_succ
  intro level
  obtain ⟨extension, extensionOld, extensionEnergy, lowerBound⟩ :=
    exists_xiWeighted_trace_of_eigenpair system rulesConnected resistanceRate resistanceRatePositive
      resistanceVector resistanceVectorPositive renormalizationEigenpair level
      (values ∘ xiVertexEmbedding system level)
  have comparison := lowerBound (values ∘ xiVertexEmbedding system (level + 1))
    (fun vertex => rfl)
  exact comparison

/-- Original connected distance-positive rule graphs supply both the positive
parameters and every attained weighted trace identity; neither is hypothesized. -/
theorem exists_xiWeighted_trace (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ resistanceRate : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ resistanceRatePositive : 0 < resistanceRate,
      ∃ resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour,
      (∀ level (oldValues : XiVtx system level → ℝ),
        ∃ extension : XiVtx system (level + 1) → ℝ,
          (∀ vertex, extension (Sum.inl vertex) = oldValues vertex) ∧
          (xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector
            resistanceVectorPositive (level + 1)).energy extension =
            (xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector
              resistanceVectorPositive level).energy oldValues ∧
          (∀ competitor : XiVtx system (level + 1) → ℝ,
            (∀ vertex, competitor (Sum.inl vertex) = oldValues vertex) →
            (xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector
              resistanceVectorPositive level).energy oldValues ≤
              (xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector
                resistanceVectorPositive (level + 1)).energy competitor)) ∧
      (∀ values : XiVertexUnion system → ℝ,
        Monotone (fun level =>
          (xiUnionWeightedNetwork system resistanceRate resistanceRatePositive resistanceVector
            resistanceVectorPositive level).energy values)) := by
  have coloursPositive : 0 < K := lt_of_le_of_lt (Nat.zero_le system.initCol.val) system.initCol.isLt
  obtain ⟨resistanceVector, resistanceRate, vectorPositive, ratePositive, normalized, eigenpair⟩ :=
    (system.connectedRuleSystem rulesConnected).distance_positive_eigenpair coloursPositive distancePositive
  have coordinateEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour =
        resistanceRate * resistanceVector colour := by
    intro colour
    exact congrFun eigenpair colour
  refine ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, ?_, ?_⟩
  · exact exists_xiWeighted_trace_of_eigenpair system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive coordinateEigenpair
  · exact xiUnionWeightedNetwork_energy_increasing_of_eigenpair system rulesConnected
      resistanceRate ratePositive resistanceVector vectorPositive coordinateEigenpair

end EIGS
