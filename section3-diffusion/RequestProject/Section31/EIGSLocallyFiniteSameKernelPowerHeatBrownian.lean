import RequestProject.Section31.EIGSOriginalMeasuredGHPSHuntPowerHeat
import RequestProject.Section31.EIGSLocallyFiniteNativeBallMass
import RequestProject.Section31.EIGSLocallyFiniteRuleResistance
import RequestProject.Section31.EIGSResistanceFormSameClosedHunt
import RequestProject.Section31.EIGSActualRecurrenceCriterion

/-! Actual Laakso (false) and canonical Xi (true) pure-power heat/Brownian
consumers. One native discrete resistance/vector/clock witness supplies the
original GHPS/Hunt family and every kernel bound. The literal bounded-degree
volume estimate is supplied internally. No volume, stay, heat or process
identity conclusion remains an input. The actual resistance form is the
original closed form of this identical Hunt family. -/
namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical NNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 12000000

theorem exists_locallyFiniteRuleSystem_same_kernel_power_heat_Brownian (canonical : Bool) :
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
    normalization, normalizationPositive, normalizedConvergence, discreteProperties⟩ :=
      exists_xiNativeSupDiscreteConvergence_of_rules system connected
        (locallyFiniteRuleSystem_loopless canonical) (locallyFiniteRuleSystem_edgesUnique canonical)
        (locallyFiniteRuleSystem_plantingNonadjacent canonical) (locallyFiniteRuleSystem_distancePositive canonical)
  have pathProperties := xiIdentifiedOriginalCommonPathTransportProperties_of_discrete system connected
    (locallyFiniteRuleSystem_loopless canonical) (locallyFiniteRuleSystem_edgesUnique canonical)
    (locallyFiniteRuleSystem_plantingNonadjacent canonical) (locallyFiniteRuleSystem_distancePositive canonical)
    resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive discreteProperties
  have globalProperties := xiIdentifiedOriginalCommonGlobalJ1Properties_of_transport system connected
    (locallyFiniteRuleSystem_loopless canonical) (locallyFiniteRuleSystem_edgesUnique canonical)
    (locallyFiniteRuleSystem_plantingNonadjacent canonical) (locallyFiniteRuleSystem_distancePositive canonical)
    resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive pathProperties
  have measuredProperties := xiIdentifiedOriginalMeasuredGHPSProperties_of_globalJ1 system connected
    (locallyFiniteRuleSystem_loopless canonical) (locallyFiniteRuleSystem_edgesUnique canonical)
    (locallyFiniteRuleSystem_plantingNonadjacent canonical) (locallyFiniteRuleSystem_distancePositive canonical)
    resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive globalProperties
  have jointProperties := xiIdentifiedOriginalMeasuredGHPSHuntHeatProperties_of_measured system connected
    (locallyFiniteRuleSystem_loopless canonical) (locallyFiniteRuleSystem_edgesUnique canonical)
    (locallyFiniteRuleSystem_plantingNonadjacent canonical) (locallyFiniteRuleSystem_distancePositive canonical)
    resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive measuredProperties
  have powerProperties := xiSameKernelPowerHeatEstimatesProperties_of_discrete_and_volume system connected
    (locallyFiniteRuleSystem_loopless canonical) (locallyFiniteRuleSystem_edgesUnique canonical)
    (locallyFiniteRuleSystem_plantingNonadjacent canonical) (locallyFiniteRuleSystem_distancePositive canonical)
    resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive
    (locallyFiniteRuleSystem_native_ball_mass_upper canonical) discreteProperties
  have jointPowerProperties := xiIdentifiedOriginalMeasuredGHPSHuntPowerHeatProperties_of_joint_and_power system connected
    (locallyFiniteRuleSystem_loopless canonical) (locallyFiniteRuleSystem_edgesUnique canonical)
    (locallyFiniteRuleSystem_plantingNonadjacent canonical) (locallyFiniteRuleSystem_distancePositive canonical)
    resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive
    powerProperties jointProperties
  have rateEquality : resistanceRate = locallyFiniteRuleResistance canonical := by
    have actualPsi := congrFun (locallyFiniteRuleSystem_Psi canonical resistanceVector
      (fun colour => (vectorPositive colour).le)) (0 : Fin 1)
    have scalarEquality : locallyFiniteRuleResistance canonical * resistanceVector 0 =
        resistanceRate * resistanceVector 0 := actualPsi.symm.trans (eigenpair 0)
    exact (mul_right_cancel₀ (vectorPositive 0).ne' scalarEquality).symm
  have rateGreaterThanOne : 1 < resistanceRate := by
    rw [rateEquality]
    cases canonical <;> norm_num [locallyFiniteRuleResistance]
  have oneColourDistance : (1 : ℕ) = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (connected colour).one_lt_dist_of_ne_of_not_adj
      (system.plant_ne colour) (locallyFiniteRuleSystem_plantingNonadjacent canonical colour)
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, eigenpair,
    normalization, normalizationPositive, normalizedConvergence, rateEquality, rateGreaterThanOne,
    ?_, ?_, jointProperties, jointPowerProperties, powerProperties, ?_⟩
  · exact exists_xiContinuousResistanceFormRealization_of_rules system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair (xiVertexEmbedding system 0 true)
      (locallyFiniteRuleSystem_loopless canonical) (locallyFiniteRuleSystem_edgesUnique canonical)
      (locallyFiniteRuleSystem_plantingNonadjacent canonical) (locallyFiniteRuleSystem_distancePositive canonical)
      oneColourDistance mass rateGreaterThanOne
  · exact xiResistanceFormClosedIdentification_of_rules system connected
      (locallyFiniteRuleSystem_loopless canonical) (locallyFiniteRuleSystem_edgesUnique canonical)
      (locallyFiniteRuleSystem_plantingNonadjacent canonical) (locallyFiniteRuleSystem_distancePositive canonical)
      oneColourDistance parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass resistanceRate ratePositive
      rateGreaterThanOne resistanceVector vectorPositive eigenpair
  · apply (xiActualRecurrent_iff_resistanceSpectralRadius_gt_one system connected
      (locallyFiniteRuleSystem_loopless canonical) (locallyFiniteRuleSystem_edgesUnique canonical)
      (locallyFiniteRuleSystem_plantingNonadjacent canonical) (locallyFiniteRuleSystem_distancePositive canonical)).mpr
    rw [← system.resistanceSpectralRadius_eq_of_positive_eigenpair connected
      (locallyFiniteRuleSystem_distancePositive canonical) ratePositive vectorPositive (funext eigenpair)]
    exact rateGreaterThanOne

end
end EIGS

#print axioms EIGS.exists_locallyFiniteRuleSystem_same_kernel_power_heat_Brownian
