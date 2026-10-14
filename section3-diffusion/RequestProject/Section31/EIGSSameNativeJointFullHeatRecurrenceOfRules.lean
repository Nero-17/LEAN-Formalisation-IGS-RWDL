import RequestProject.Section31.EIGSSameNativeJointFullHeatEstimatesOfRules
import RequestProject.Section31.EIGSActualRecurrenceSpectralThreshold

/-! The actual fractional-eccentricity graph recurrence criterion uses
the same spectral value as the retained process kernel's physical AE
dimension. The resistance eigenpair and clock are chosen only once by the
full heat-estimates consumer. Candidate source, awaiting compilation. -/

namespace EIGS
open MeasureTheory Filter Topology
open scoped Classical NNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 9000000
variable {K : ℕ}

theorem xiActualRecurrent_iff_same_resistance_spectral_formula_lt_two (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour) :
    let mass := xiMassParametersOfRules system rulesConnected distancePositive
    xiActualRecurrent system ↔
      2 * (Real.log mass.rate / Real.log (mass.rate * resistanceRate)) < 2 := by
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  have rateEquality := system.resistanceSpectralRadius_eq_of_positive_eigenpair
    rulesConnected distancePositive ratePositive vectorPositive (funext renormalizationEigenpair)
  have criterion := xiActualRecurrent_iff_globalSpectralFormula_lt_two system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive
  rw [← XiMassParameters.rate_eq_spectralRadius system mass, ← rateEquality] at criterion
  simpa only [mul_div_assoc] using criterion
theorem exists_xiSameNativeJointFullHeatEstimatesRecurrence_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (primitiveDegree : (degreeMatrix system).IsPrimitive)
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
    exists_xiSameNativeJointFullHeatEstimates_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent primitiveDegree distancePositive
  exact ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, jointProperties, heatEstimates,
    xiActualRecurrent_iff_same_resistance_spectral_formula_lt_two system rulesConnected
      rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive
      resistanceVector vectorPositive renormalizationEigenpair⟩

end
end EIGS

#print axioms EIGS.xiActualRecurrent_iff_same_resistance_spectral_formula_lt_two
#print axioms EIGS.exists_xiSameNativeJointFullHeatEstimatesRecurrence_of_rules
