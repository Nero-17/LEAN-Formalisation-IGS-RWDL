import RequestProject.Section31.EIGSLocallyFiniteSameKernelPowerHeatExitPhysical
import RequestProject.Section31.EIGSOriginalPowerHeatExitPhysicalTight

/-! Actual locally finite Brownian/pure-power/true-exit/Poisson weak laws
and uniform tightness share their original resistance, clock, Hunt family,
kernel and GHPS ambient. No additional witness or target assumption. -/
namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical NNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 12000000
theorem exists_locallyFiniteRuleSystem_same_kernel_power_heat_exit_physical_tight_Brownian (canonical : Bool) :
    let system := locallyFiniteRuleSystem canonical
    let connected := locallyFiniteRuleSystem_connected canonical
    let parameters := xiPathMetricDataOfRules system connected
      (locallyFiniteRuleSystem_loopless canonical) (locallyFiniteRuleSystem_edgesUnique canonical)
      (locallyFiniteRuleSystem_distancePositive canonical)
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius connected (locallyFiniteRuleSystem_edgesUnique canonical)
          (locallyFiniteRuleSystem_plantingNonadjacent canonical) (locallyFiniteRuleSystem_distancePositive canonical))
    let mass := xiMassParametersOfRules system connected (locallyFiniteRuleSystem_distancePositive canonical)
    letI := xiCompletion_compactSpace system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair
    ∃ resistanceRate : ℝ, ∃ ratePositive : 0 < resistanceRate,
    ∃ resistanceVector : Fin 1 → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
    ∃ eigenpair : ∀ colour, (system.ruleFamily connected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour,
    ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
      Tendsto (fun offset => fun colour =>
        (system.ruleFamily connected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (𝓝 (normalization • resistanceVector)) ∧
      resistanceRate = locallyFiniteRuleResistance canonical ∧
      1 < resistanceRate ∧
      Nonempty (XiContinuousResistanceFormRealization system connected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair resistanceRate ratePositive
        resistanceVector vectorPositive eigenpair (xiVertexEmbedding system 0 true)) ∧
      XiResistanceFormClosedIdentification system connected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass resistanceRate ratePositive
        resistanceVector vectorPositive eigenpair ∧
      XiIdentifiedOriginalMeasuredGHPSPowerHeatExitPhysicalTightProperties system connected
        (locallyFiniteRuleSystem_loopless canonical) (locallyFiniteRuleSystem_edgesUnique canonical)
        (locallyFiniteRuleSystem_plantingNonadjacent canonical) (locallyFiniteRuleSystem_distancePositive canonical)
        resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive ∧
      XiIdentifiedOriginalMeasuredGHPSPowerHeatExitPhysicalProperties system connected
        (locallyFiniteRuleSystem_loopless canonical) (locallyFiniteRuleSystem_edgesUnique canonical)
        (locallyFiniteRuleSystem_plantingNonadjacent canonical) (locallyFiniteRuleSystem_distancePositive canonical)
        resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive ∧
      XiIdentifiedOriginalMeasuredGHPSHuntHeatProperties system connected
        (locallyFiniteRuleSystem_loopless canonical) (locallyFiniteRuleSystem_edgesUnique canonical)
        (locallyFiniteRuleSystem_plantingNonadjacent canonical) (locallyFiniteRuleSystem_distancePositive canonical)
        resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive ∧
      XiIdentifiedOriginalMeasuredGHPSHuntPowerHeatProperties system connected
        (locallyFiniteRuleSystem_loopless canonical) (locallyFiniteRuleSystem_edgesUnique canonical)
        (locallyFiniteRuleSystem_plantingNonadjacent canonical) (locallyFiniteRuleSystem_distancePositive canonical)
        resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive ∧
      XiSameKernelPowerHeatEstimatesProperties system connected
        (locallyFiniteRuleSystem_loopless canonical) (locallyFiniteRuleSystem_edgesUnique canonical)
        (locallyFiniteRuleSystem_plantingNonadjacent canonical) (locallyFiniteRuleSystem_distancePositive canonical)
        resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive ∧
      xiActualRecurrent system := by
  intro system connected parameters distanceGreaterThanOne mass
  letI := xiCompletion_compactSpace system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, eigenpair,
    normalization, normalizationPositive, normalizedConvergence, rateEquality, rateGreaterThanOne,
    realization, closedIdentification, physicalProperties, jointProperties, jointPowerProperties,
    powerProperties, recurrence⟩ :=
      exists_locallyFiniteRuleSystem_same_kernel_power_heat_exit_physical_Brownian canonical
  have tightProperties := xiIdentifiedOriginalMeasuredGHPSPowerHeatExitPhysicalTightProperties_of_physical system connected
    (locallyFiniteRuleSystem_loopless canonical) (locallyFiniteRuleSystem_edgesUnique canonical)
    (locallyFiniteRuleSystem_plantingNonadjacent canonical) (locallyFiniteRuleSystem_distancePositive canonical)
    resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive physicalProperties
  exact ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, eigenpair,
    normalization, normalizationPositive, normalizedConvergence, rateEquality, rateGreaterThanOne,
    realization, closedIdentification, tightProperties, physicalProperties, jointProperties,
    jointPowerProperties, powerProperties, recurrence⟩

end
end EIGS

#print axioms EIGS.exists_locallyFiniteRuleSystem_same_kernel_power_heat_exit_physical_tight_Brownian
