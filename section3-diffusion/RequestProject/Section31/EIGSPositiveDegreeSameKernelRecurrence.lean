import RequestProject.Section31.EIGSSameNativeJointFullHeatRecurrenceOfRules
import RequestProject.Section31.EIGSPositiveDegreeSameKernelFullHeat

/-! Positive degree eigenpair version on the original state space, measure,
closed form and semigroup. Existing universal heat-property definitions are
retained verbatim. Candidate source; no compilation is claimed. -/

namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
open scoped BigOperators Classical BoundedContinuousFunction ENNReal
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

theorem exists_xiSameNativeJointFullHeatEstimatesRecurrence_of_rules_of_positive_degree_data (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (degreeData : XiPositiveDegreeSpectralData system)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ resistanceRate : ℝ, ∃ ratePositive : 0 < resistanceRate,
      ∃ resistanceVector : Fin K → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
      Tendsto (fun offset => fun colour =>
        (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (𝓝 (normalization • resistanceVector)) ∧
      XiIdentifiedOriginalMeasuredGHPSHuntHeatProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
        normalization normalizationPositive ∧
      XiSameKernelFullHeatEstimatesProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
        normalization normalizationPositive ∧
      (let mass := xiMassParametersOfRules system rulesConnected distancePositive;
        xiActualRecurrent system ↔
          2 * (Real.log mass.rate / Real.log (mass.rate * resistanceRate)) < 2) := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, jointProperties, heatEstimates⟩ :=
    exists_xiSameNativeJointFullHeatEstimates_of_rules_of_positive_degree_data system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent degreeData distancePositive
  exact ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, jointProperties, heatEstimates,
    xiActualRecurrent_iff_same_resistance_spectral_formula_lt_two system rulesConnected
      rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive
      resistanceVector vectorPositive renormalizationEigenpair⟩


end
end EIGS

#print axioms EIGS.exists_xiSameNativeJointFullHeatEstimatesRecurrence_of_rules_of_positive_degree_data

