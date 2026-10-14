import RequestProject.Section31.EIGSPositiveDegreeSameKernelBrownian
import RequestProject.Section31.EIGSTwoColourPositiveDegreeData
import RequestProject.Section31.EIGSTwoColourActualSpectralParameters

/-! Literal Figure 3 Brownian/full-heat realization. The actual graph supplies
its positive degree data internally although its degree matrix is not primitive.
A single native-limit witness supplies the original GHPS laws, the original
closed form, the resistance-form Brownian motion and their same heat kernel.
Candidate source. -/

namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
open scoped BigOperators Classical BoundedContinuousFunction ENNReal
noncomputable section
set_option maxHeartbeats 5000000

theorem exists_twoColour_same_kernel_Brownian_full_heat :
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
      Nonempty (XiContinuousResistanceFormRealization twoColourSystem twoColourSystem_connected parameters.lengths parameters.lengthsPositive
        (twoColourSystem.distanceSpectralRadius twoColourSystem_connected) distanceGreaterThanOne parameters.eigenpair resistanceRate ratePositive
        resistanceVector vectorPositive eigenpair (xiVertexEmbedding twoColourSystem 0 true)) ∧
      XiResistanceFormClosedIdentification twoColourSystem twoColourSystem_connected parameters.lengths parameters.lengthsPositive
        (twoColourSystem.distanceSpectralRadius twoColourSystem_connected) distanceGreaterThanOne parameters.eigenpair mass resistanceRate ratePositive
        resistanceVector vectorPositive eigenpair ∧
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
  have canonicalRateGreaterThanOne : 1 < twoColourSystem.resistanceSpectralRadius
      twoColourSystem_connected twoColourSystem_distancePositive := by
    rw [twoColourSystem_resistanceSpectralRadius]
    exact twoColourResistanceRate_greaterThanOne
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, eigenpair,
      normalization, normalizationPositive, normalizedConvergence, rateGreaterThanOne, remaining⟩ :=
    exists_xiResistanceBrownian_same_kernel_full_heat_recurrence_of_rules_of_positive_degree_data
      twoColourSystem twoColourSystem_connected twoColourSystem_loopless twoColourSystem_edgesUnique
      twoColourSystem_plantingNonadjacent twoColourPositiveDegreeData twoColourSystem_distancePositive
      canonicalRateGreaterThanOne
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, eigenpair,
    normalization, normalizationPositive, normalizedConvergence, rateGreaterThanOne, ?_, remaining⟩
  exact (twoColourSystem.resistanceSpectralRadius_eq_of_positive_eigenpair twoColourSystem_connected
    twoColourSystem_distancePositive ratePositive vectorPositive (funext eigenpair)).trans
      twoColourSystem_resistanceSpectralRadius

end
end EIGS

#print axioms EIGS.exists_twoColour_same_kernel_Brownian_full_heat

