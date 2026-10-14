import RequestProject.Section31.EIGSSameNativeJointFullHeatExitRecurrenceOfRules
import RequestProject.Section31.EIGSPositiveDegreeSameKernelRecurrence

/-! The same native witness gains actual native/normalized true-exit survival
and mean-exit properties through the accepted primitive-free converter.
No independent Hunt process or target exit estimate is selected. Candidate. -/

namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 12000000
variable {K : ℕ}

theorem exists_xiSameNativeJointFullHeatExitRecurrence_of_rules_of_positive_degree_data (system : EIGSData K)
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
      ∃ eigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
        Tendsto (fun offset => fun colour =>
          (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
          atTop (𝓝 (normalization • resistanceVector)) ∧
        XiIdentifiedOriginalMeasuredGHPSFullHeatExitProperties system rulesConnected rulesLoopless rulesUnique
          plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
          eigenpair normalization normalizationPositive ∧
        XiIdentifiedOriginalMeasuredGHPSHuntHeatProperties system rulesConnected rulesLoopless rulesUnique
          plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
          eigenpair normalization normalizationPositive ∧
        XiSameKernelFullHeatEstimatesProperties system rulesConnected rulesLoopless rulesUnique
          plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
          eigenpair normalization normalizationPositive ∧
        (let mass := xiMassParametersOfRules system rulesConnected distancePositive;
          xiActualRecurrent system ↔ 2 * (Real.log mass.rate / Real.log (mass.rate * resistanceRate)) < 2) := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, eigenpair,
    normalization, normalizationPositive, normalizedConvergence, jointProperties, heatEstimates, recurrence⟩ :=
    exists_xiSameNativeJointFullHeatEstimatesRecurrence_of_rules_of_positive_degree_data system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent degreeData distancePositive
  exact ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, eigenpair,
    normalization, normalizationPositive, normalizedConvergence,
    xiIdentifiedOriginalMeasuredGHPSFullHeatExitProperties_of_full_heat system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair normalization normalizationPositive jointProperties heatEstimates,
    jointProperties, heatEstimates, recurrence⟩


end
end EIGS

#print axioms EIGS.exists_xiSameNativeJointFullHeatExitRecurrence_of_rules_of_positive_degree_data

