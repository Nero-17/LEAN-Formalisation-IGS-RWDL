import RequestProject.Section31.EIGSUVFlowerCanonicalResistance
import RequestProject.Section31.EIGSUVFlowerDegreeSpectrum
import RequestProject.Section31.EIGSUVFlowerDistanceSpectrum
import RequestProject.Section31.EIGSOriginalDegreeFullHeatPhysicalOfRules
import RequestProject.Section31.EIGSOriginalFullHeatExitPhysicalTight
import RequestProject.Section31.EIGSNumericalSameKernelFullHeatEstimates

/-! Actual unequal-path flower consumers. The original rule-only Hunt
witness is selected once. Degree statistics, exact heat exponents,
physical Poisson laws, true exits and tightness all use this witness.
The resistance-form branch is supplied precisely when u*v > u+v;
the (2,2) flower is not asserted to lie in that branch. -/
namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical NNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 12000000

theorem exists_uvFlowerSystem_same_kernel_full_heat_physical_tight
    (firstLength secondLength : ℕ)
    (firstAtLeastTwo : 2 ≤ firstLength) (secondAtLeastTwo : 2 ≤ secondLength) :
    let system := uvFlowerSystem firstLength secondLength
    let connected := uvFlowerSystem_connected firstLength secondLength (by omega) (by omega)
    let loopless := uvFlowerSystem_loopless firstLength secondLength
    let unique := uvFlowerSystem_edgesUnique firstLength secondLength firstAtLeastTwo secondAtLeastTwo
    let nonadjacent := uvFlowerSystem_plantingNonadjacent firstLength secondLength firstAtLeastTwo secondAtLeastTwo
    let distancePositive := uvFlowerSystem_distancePositive firstLength secondLength
    let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius connected unique nonadjacent distancePositive)
    let mass := xiMassParametersOfRules system connected distancePositive
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
        resistanceRate = uvFlowerRuleResistance firstLength secondLength ∧
        mass.rate * resistanceRate = (firstLength : ℝ) * secondLength ∧
        XiIdentifiedOriginalDegreeCorrectedPhysicalProperties system connected loopless unique nonadjacent
          distancePositive resistanceRate ratePositive resistanceVector vectorPositive eigenpair
          normalization normalizationPositive ∧
        XiIdentifiedOriginalMeasuredGHPSFullHeatExitPhysicalTightProperties system connected loopless unique
          nonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive eigenpair
          normalization normalizationPositive ∧
        XiIdentifiedOriginalMeasuredGHPSFullHeatExitPhysicalProperties system connected loopless unique
          nonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive eigenpair
          normalization normalizationPositive ∧
        XiIdentifiedOriginalMeasuredGHPSHuntHeatProperties system connected loopless unique nonadjacent
          distancePositive resistanceRate ratePositive resistanceVector vectorPositive eigenpair
          normalization normalizationPositive ∧
        XiNumericalSameKernelFullHeatEstimatesProperties system connected loopless unique nonadjacent
          distancePositive resistanceRate ratePositive resistanceVector vectorPositive eigenpair
          normalization normalizationPositive
          ((Real.log ((firstLength : ℝ) + secondLength) - Real.log 2) /
            Real.log ((firstLength : ℝ) * secondLength))
          (Real.log ((firstLength : ℝ) + secondLength) / Real.log ((firstLength : ℝ) * secondLength))
          (1 / (Real.log ((firstLength : ℝ) + secondLength) / Real.log 2 - 1)) ∧
        (xiActualRecurrent system ↔ (firstLength : ℝ) + secondLength < (firstLength : ℝ) * secondLength) ∧
        ((firstLength : ℝ) + secondLength < (firstLength : ℝ) * secondLength →
          Nonempty (XiContinuousResistanceFormRealization system connected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair resistanceRate ratePositive
            resistanceVector vectorPositive eigenpair (xiVertexEmbedding system 0 true)) ∧
          XiResistanceFormClosedIdentification system connected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass resistanceRate ratePositive
            resistanceVector vectorPositive eigenpair) := by
  intro system connected loopless unique nonadjacent distancePositive parameters distanceGreaterThanOne mass
  letI := xiCompletion_compactSpace system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, eigenpair,
    normalization, normalizationPositive, normalizedConvergence, correctedProperties, physicalProperties,
    unitProperties, exitProperties, jointProperties, heatEstimates, recurrence⟩ :=
      exists_xiSameNativeOriginalDegreeCorrectedFullHeatPhysical_of_rules system connected loopless unique nonadjacent
        (uvFlowerSystem_degreeMatrix_primitive firstLength secondLength (by omega) (by omega)) distancePositive
  have rateEquality : resistanceRate = uvFlowerRuleResistance firstLength secondLength := by
    have actualPsi := congrFun (uvFlowerSystem_Psi firstLength secondLength (by omega) (by omega)
      resistanceVector (fun colour => (vectorPositive colour).le)) (0 : Fin 1)
    have scalarEquality : uvFlowerRuleResistance firstLength secondLength * resistanceVector 0 =
        resistanceRate * resistanceVector 0 := actualPsi.symm.trans (eigenpair 0)
    exact (mul_right_cancel₀ (vectorPositive 0).ne' scalarEquality).symm
  have massEquality : mass.rate = (firstLength : ℝ) + secondLength :=
    (XiMassParameters.rate_eq_spectralRadius system mass).trans
      (uvFlowerSystem_massSpectralRadius firstLength secondLength)
  have degreeEquality : finiteRealMatrixSpectralRadius (degreeMatrix system) = 2 :=
    uvFlowerSystem_degreeSpectralRadius firstLength secondLength (by omega) (by omega)
  have denominatorPositive : 0 < (firstLength : ℝ) + secondLength :=
    add_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr (by omega))
  have timeRateEquality : mass.rate * resistanceRate = (firstLength : ℝ) * secondLength := by
    rw [massEquality, rateEquality]
    unfold uvFlowerRuleResistance
    field_simp [denominatorPositive.ne']
  have tightProperties := xiIdentifiedOriginalMeasuredGHPSFullHeatExitPhysicalTightProperties_of_physical
    system connected loopless unique nonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive eigenpair normalization normalizationPositive physicalProperties
  have numericalEstimates := xiNumericalSameKernelFullHeatEstimatesProperties_of_canonical
    system connected loopless unique nonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive eigenpair normalization normalizationPositive
    ((Real.log ((firstLength : ℝ) + secondLength) - Real.log 2) /
      Real.log ((firstLength : ℝ) * secondLength))
    (Real.log ((firstLength : ℝ) + secondLength) / Real.log ((firstLength : ℝ) * secondLength))
    (1 / (Real.log ((firstLength : ℝ) + secondLength) / Real.log 2 - 1))
    (by rw [timeRateEquality, massEquality, degreeEquality])
    (by rw [timeRateEquality, massEquality])
    (by rw [massEquality, degreeEquality]) heatEstimates
  have brownianCriterion : 1 < resistanceRate ↔
      (firstLength : ℝ) + secondLength < (firstLength : ℝ) * secondLength := by
    rw [rateEquality, uvFlowerRuleResistance, lt_div_iff₀ denominatorPositive, one_mul]
  have actualRecurrence : xiActualRecurrent system ↔
      (firstLength : ℝ) + secondLength < (firstLength : ℝ) * secondLength := by
    rw [xiActualRecurrent_iff_resistanceSpectralRadius_gt_one system connected loopless unique
      nonadjacent distancePositive,
      ← system.resistanceSpectralRadius_eq_of_positive_eigenpair connected distancePositive
        ratePositive vectorPositive (funext eigenpair)]
    exact brownianCriterion
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, eigenpair,
    normalization, normalizationPositive, normalizedConvergence, rateEquality, timeRateEquality,
    correctedProperties, tightProperties, physicalProperties, jointProperties, numericalEstimates,
    actualRecurrence, ?_⟩
  intro arithmeticSupercritical
  have rateGreaterThanOne := brownianCriterion.mpr arithmeticSupercritical
  have oneColourDistance : (1 : ℕ) = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (connected colour).one_lt_dist_of_ne_of_not_adj (system.plant_ne colour) (nonadjacent colour)
  constructor
  · exact exists_xiContinuousResistanceFormRealization_of_rules system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair (xiVertexEmbedding system 0 true)
      loopless unique nonadjacent distancePositive oneColourDistance mass rateGreaterThanOne
  · exact xiResistanceFormClosedIdentification_of_rules system connected loopless unique nonadjacent distancePositive
      oneColourDistance parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected)
      distanceGreaterThanOne parameters.eigenpair mass resistanceRate ratePositive rateGreaterThanOne
      resistanceVector vectorPositive eigenpair

end
end EIGS

#print axioms EIGS.exists_uvFlowerSystem_same_kernel_full_heat_physical_tight
