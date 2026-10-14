import RequestProject.Section31.EIGSResistanceBrownianSameKernelFullHeatOfRules
import RequestProject.Section31.EIGSPositiveDegreeSameKernelRecurrence

/-! Positive degree eigenpair version on the original state space, measure,
closed form and semigroup. Existing universal heat-property definitions are
retained verbatim. Candidate source; no compilation is claimed. -/

namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
open scoped BigOperators Classical BoundedContinuousFunction ENNReal
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

theorem exists_xiResistanceBrownian_same_kernel_full_heat_recurrence_of_rules_of_positive_degree_data
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (degreeData : XiPositiveDegreeSpectralData system)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (canonicalRateGreaterThanOne : 1 < system.resistanceSpectralRadius rulesConnected distancePositive) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system rulesConnected distancePositive
    letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
    ∃ resistanceRate : ℝ, ∃ ratePositive : 0 < resistanceRate,
    ∃ resistanceVector : Fin K → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
    ∃ eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
    ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
      Tendsto (fun offset => fun colour =>
        (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (𝓝 (normalization • resistanceVector)) ∧
      1 < resistanceRate ∧
      Nonempty (XiContinuousResistanceFormRealization system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair resistanceRate ratePositive
        resistanceVector vectorPositive eigenpair (xiVertexEmbedding system 0 true)) ∧
      XiResistanceFormClosedIdentification system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass resistanceRate ratePositive
        resistanceVector vectorPositive eigenpair ∧
      XiIdentifiedOriginalMeasuredGHPSBrownianFullHeatProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive ∧
      XiIdentifiedOriginalMeasuredGHPSHuntHeatProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive ∧
      XiSameKernelFullHeatEstimatesProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive ∧
      (xiActualRecurrent system ↔ 2 * (Real.log mass.rate / Real.log (mass.rate * resistanceRate)) < 2) := by
  intro parameters distanceGreaterThanOne mass
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, eigenpair,
      normalization, normalizationPositive, normalizedConvergence, jointProperties, heatEstimates, recurrence⟩ :=
    exists_xiSameNativeJointFullHeatEstimatesRecurrence_of_rules_of_positive_degree_data system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent degreeData distancePositive
  have canonicalEquality := system.resistanceSpectralRadius_eq_of_positive_eigenpair rulesConnected distancePositive
    ratePositive vectorPositive (funext eigenpair)
  have rateGreaterThanOne : 1 < resistanceRate := by
    rw [canonicalEquality]
    exact canonicalRateGreaterThanOne
  have oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj (system.plant_ne colour) (plantingNonadjacent colour)
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, eigenpair,
    normalization, normalizationPositive, normalizedConvergence, rateGreaterThanOne, ?_, ?_, ?_,
    jointProperties, heatEstimates, recurrence⟩
  · exact exists_xiContinuousResistanceFormRealization_of_rules system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair resistanceRate ratePositive resistanceVector
      vectorPositive eigenpair (xiVertexEmbedding system 0 true) rulesLoopless rulesUnique plantingNonadjacent distancePositive
      oneColourDistance mass rateGreaterThanOne
  · exact xiResistanceFormClosedIdentification_of_rules system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair mass resistanceRate ratePositive rateGreaterThanOne resistanceVector vectorPositive eigenpair
  · exact xiIdentifiedOriginalMeasuredGHPSBrownianFullHeatProperties_of_full_heat system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive eigenpair
      normalization normalizationPositive jointProperties heatEstimates


end
end EIGS

#print axioms EIGS.exists_xiResistanceBrownian_same_kernel_full_heat_recurrence_of_rules_of_positive_degree_data

