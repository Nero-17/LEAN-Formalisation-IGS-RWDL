import RequestProject.Section31.EIGSResistanceBrownianSameKernelFullHeatExitOfRules
import RequestProject.Section31.EIGSTwoColourSameKernelBrownianFullHeat

/-! Direct upgrade of the accepted literal Figure 3 full-heat numerical
witness. The same resistance vector/rate/time normalization and the same
original joint/full-heat data supply true-exit estimates. Brownian full-heat
identification is read from that exit bundle, so no Hunt is spliced. Candidate. -/

namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 12000000

theorem exists_twoColour_same_kernel_Brownian_full_heat_exit :
    let parameters := xiPathMetricDataOfRules twoColourSystem twoColourSystem_connected twoColourSystem_loopless twoColourSystem_edgesUnique twoColourSystem_distancePositive
    let distanceGreaterThanOne : 1 < twoColourSystem.distanceSpectralRadius twoColourSystem_connected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (twoColourSystem.two_le_distanceSpectralRadius twoColourSystem_connected twoColourSystem_edgesUnique twoColourSystem_plantingNonadjacent twoColourSystem_distancePositive)
    let mass := xiMassParametersOfRules twoColourSystem twoColourSystem_connected twoColourSystem_distancePositive
    letI := xiCompletion_compactSpace twoColourSystem twoColourSystem_connected parameters.lengths parameters.lengthsPositive
      (twoColourSystem.distanceSpectralRadius twoColourSystem_connected) distanceGreaterThanOne parameters.eigenpair
    ∃ resistanceRate : ℝ, ∃ ratePositive : 0 < resistanceRate,
    ∃ resistanceVector : Fin 2 → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
    ∃ eigenpair : ∀ colour, (twoColourSystem.ruleFamily twoColourSystem_connected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
    ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
      Tendsto (fun offset => fun colour =>
        (twoColourSystem.ruleFamily twoColourSystem_connected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (𝓝 (normalization • resistanceVector)) ∧
      1 < resistanceRate ∧
      resistanceRate = twoColourResistanceRate ∧
      ((1.1159 : ℝ) < 2 * (Real.log mass.rate - Real.log 2) / Real.log (mass.rate * resistanceRate) ∧
        2 * (Real.log mass.rate - Real.log 2) / Real.log (mass.rate * resistanceRate) < 1.1161) ∧
      ((1.8876 : ℝ) < 2 * Real.log mass.rate / Real.log (mass.rate * resistanceRate) ∧
        2 * Real.log mass.rate / Real.log (mass.rate * resistanceRate) < 1.8878) ∧
      Nonempty (XiContinuousResistanceFormRealization twoColourSystem twoColourSystem_connected parameters.lengths parameters.lengthsPositive
        (twoColourSystem.distanceSpectralRadius twoColourSystem_connected) distanceGreaterThanOne parameters.eigenpair resistanceRate ratePositive
        resistanceVector vectorPositive eigenpair (xiVertexEmbedding twoColourSystem 0 true)) ∧
      XiResistanceFormClosedIdentification twoColourSystem twoColourSystem_connected parameters.lengths parameters.lengthsPositive
        (twoColourSystem.distanceSpectralRadius twoColourSystem_connected) distanceGreaterThanOne parameters.eigenpair mass resistanceRate ratePositive
        resistanceVector vectorPositive eigenpair ∧
      XiIdentifiedOriginalMeasuredGHPSFullHeatExitProperties twoColourSystem twoColourSystem_connected twoColourSystem_loopless twoColourSystem_edgesUnique twoColourSystem_plantingNonadjacent
        twoColourSystem_distancePositive resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive ∧
      XiIdentifiedOriginalMeasuredGHPSBrownianFullHeatProperties twoColourSystem twoColourSystem_connected twoColourSystem_loopless twoColourSystem_edgesUnique twoColourSystem_plantingNonadjacent
        twoColourSystem_distancePositive resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive ∧
      XiIdentifiedOriginalMeasuredGHPSHuntHeatProperties twoColourSystem twoColourSystem_connected twoColourSystem_loopless twoColourSystem_edgesUnique twoColourSystem_plantingNonadjacent
        twoColourSystem_distancePositive resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive ∧
      XiSameKernelFullHeatEstimatesProperties twoColourSystem twoColourSystem_connected twoColourSystem_loopless twoColourSystem_edgesUnique twoColourSystem_plantingNonadjacent
        twoColourSystem_distancePositive resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive ∧
      (xiActualRecurrent twoColourSystem ↔ 2 * (Real.log mass.rate / Real.log (mass.rate * resistanceRate)) < 2) := by
  intro parameters distanceGreaterThanOne mass
  letI := xiCompletion_compactSpace twoColourSystem twoColourSystem_connected parameters.lengths parameters.lengthsPositive
    (twoColourSystem.distanceSpectralRadius twoColourSystem_connected) distanceGreaterThanOne parameters.eigenpair
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, eigenpair,
    normalization, normalizationPositive, normalizedConvergence, rateGreaterThanOne, rateEquality,
    finiteNumeric, typicalNumeric, realization, closedIdentification, brownianProperties,
    jointProperties, heatEstimates, recurrence⟩ := exists_twoColour_same_kernel_Brownian_full_heat
  have exitProperties := xiIdentifiedOriginalMeasuredGHPSFullHeatExitProperties_of_full_heat twoColourSystem
    twoColourSystem_connected twoColourSystem_loopless twoColourSystem_edgesUnique twoColourSystem_plantingNonadjacent
    twoColourSystem_distancePositive resistanceRate ratePositive resistanceVector vectorPositive eigenpair
    normalization normalizationPositive jointProperties heatEstimates
  exact ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, eigenpair,
    normalization, normalizationPositive, normalizedConvergence, rateGreaterThanOne, rateEquality,
    finiteNumeric, typicalNumeric, realization, closedIdentification, exitProperties,
    xiIdentifiedOriginalMeasuredGHPSBrownianFullHeatProperties_of_full_heat_exit twoColourSystem
      twoColourSystem_connected twoColourSystem_loopless twoColourSystem_edgesUnique twoColourSystem_plantingNonadjacent
      twoColourSystem_distancePositive resistanceRate ratePositive resistanceVector vectorPositive eigenpair
      normalization normalizationPositive exitProperties,
    jointProperties, heatEstimates, recurrence⟩

end
end EIGS

#print axioms EIGS.exists_twoColour_same_kernel_Brownian_full_heat_exit

