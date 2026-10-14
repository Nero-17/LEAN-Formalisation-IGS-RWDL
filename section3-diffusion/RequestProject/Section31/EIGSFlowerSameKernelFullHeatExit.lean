import RequestProject.Section31.EIGSSameKernelNumericalHeatEstimates
import RequestProject.Section31.EIGSSameNativeJointFullHeatExitRecurrenceOfRules
import RequestProject.Section31.EIGSFlowerHeatExponents
import RequestProject.Section31.EIGSFlowerDegreePrimitive

/-! The actual flower's original full-heat and exit witness, with exact numerical
heat exponents for every literal kernel representing the same closed semigroup.
The actual canonical rates supply every scalar identity internally. -/

namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical NNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 12000000

 theorem exists_flowerSystem_sameKernel_fullHeat_exit (branches segments : ℕ)
    (branchesAtLeastTwo : 2 ≤ branches) (segmentsAtLeastTwo : 2 ≤ segments) :
    ∃ resistanceRate : ℝ, ∃ ratePositive : 0 < resistanceRate,
      ∃ resistanceVector : Fin 1 → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ eigenpair : ∀ colour,
        ((flowerSystem branches segments).ruleFamily (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo)).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
        Tendsto (fun offset => fun colour =>
          ((flowerSystem branches segments).ruleFamily (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo)).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
          atTop (𝓝 (normalization • resistanceVector)) ∧
        XiIdentifiedOriginalMeasuredGHPSFullHeatExitProperties (flowerSystem branches segments) (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo) (flowerSystem_loopless branches segments) (flowerSystem_edgesUnique branches segments segmentsAtLeastTwo)
          (flowerSystem_plantingNonadjacent branches segments segmentsAtLeastTwo) (flowerSystem_distancePositive branches segments) resistanceRate ratePositive resistanceVector vectorPositive
          eigenpair normalization normalizationPositive ∧
        XiIdentifiedOriginalMeasuredGHPSHuntHeatProperties (flowerSystem branches segments) (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo) (flowerSystem_loopless branches segments) (flowerSystem_edgesUnique branches segments segmentsAtLeastTwo)
          (flowerSystem_plantingNonadjacent branches segments segmentsAtLeastTwo) (flowerSystem_distancePositive branches segments) resistanceRate ratePositive resistanceVector vectorPositive
          eigenpair normalization normalizationPositive ∧
        XiSameKernelFullHeatEstimatesProperties (flowerSystem branches segments) (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo) (flowerSystem_loopless branches segments) (flowerSystem_edgesUnique branches segments segmentsAtLeastTwo)
          (flowerSystem_plantingNonadjacent branches segments segmentsAtLeastTwo) (flowerSystem_distancePositive branches segments) resistanceRate ratePositive resistanceVector vectorPositive
          eigenpair normalization normalizationPositive ∧
        resistanceRate = (segments : ℝ) / branches ∧
        XiSameKernelNumericalHeatEstimatesProperties (flowerSystem branches segments)
          (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo)
          (flowerSystem_loopless branches segments)
          (flowerSystem_edgesUnique branches segments segmentsAtLeastTwo)
          (flowerSystem_plantingNonadjacent branches segments segmentsAtLeastTwo)
          (flowerSystem_distancePositive branches segments)
          resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive
          (1 / 2) ((1 + Real.log branches / Real.log segments) / 2)
          (Real.log branches / Real.log segments) ∧
        (let mass := xiMassParametersOfRules (flowerSystem branches segments) (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo) (flowerSystem_distancePositive branches segments);
          xiActualRecurrent (flowerSystem branches segments) ↔ 2 * (Real.log mass.rate / Real.log (mass.rate * resistanceRate)) < 2) := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, eigenpair,
      normalization, normalizationPositive, normalizedConvergence, jointProperties,
      huntProperties, heatEstimates, recurrence⟩ :=
    exists_xiSameNativeJointFullHeatExitRecurrence_of_rules (flowerSystem branches segments)
      (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo)
      (flowerSystem_loopless branches segments)
      (flowerSystem_edgesUnique branches segments segmentsAtLeastTwo)
      (flowerSystem_plantingNonadjacent branches segments segmentsAtLeastTwo)
      (flowerSystem_degreeMatrix_primitive branches segments branchesAtLeastTwo segmentsAtLeastTwo)
      (flowerSystem_distancePositive branches segments)
  have rateEquality : resistanceRate = (segments : ℝ) / branches :=
    ((flowerSystem branches segments).resistanceSpectralRadius_eq_of_positive_eigenpair
      (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo)
      (flowerSystem_distancePositive branches segments) ratePositive vectorPositive
      (by funext colour; exact eigenpair colour)).trans
      (flowerSystem_resistanceSpectralRadius branches segments (by omega) segmentsAtLeastTwo)
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, eigenpair,
    normalization, normalizationPositive, normalizedConvergence, jointProperties,
    huntProperties, heatEstimates, rateEquality, ?_, recurrence⟩
  apply xiSameKernelNumericalHeatEstimatesProperties_of_actual
    (flowerSystem branches segments)
    (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo)
    (flowerSystem_loopless branches segments)
    (flowerSystem_edgesUnique branches segments segmentsAtLeastTwo)
    (flowerSystem_plantingNonadjacent branches segments segmentsAtLeastTwo)
    (flowerSystem_distancePositive branches segments)
    resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive
    (1 / 2) ((1 + Real.log branches / Real.log segments) / 2)
    (Real.log branches / Real.log segments) _ _ _ heatEstimates
  all_goals
    rw [XiMassParameters.rate_eq_spectralRadius, flowerSystem_massSpectralRadius]
  · rw [flowerSystem_degreeSpectralRadius branches segments (by omega) (by omega), rateEquality]
    exact (flowerSystem_heat_exponent_values branches segments branchesAtLeastTwo segmentsAtLeastTwo).1
  · rw [rateEquality]
    exact (flowerSystem_heat_exponent_values branches segments branchesAtLeastTwo segmentsAtLeastTwo).2.1
  · rw [flowerSystem_degreeSpectralRadius branches segments (by omega) (by omega)]
    exact (flowerSystem_heat_exponent_values branches segments branchesAtLeastTwo segmentsAtLeastTwo).2.2

end
end EIGS

#print axioms EIGS.exists_flowerSystem_sameKernel_fullHeat_exit
