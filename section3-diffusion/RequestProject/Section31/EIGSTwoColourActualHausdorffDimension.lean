import RequestProject.Section31.EIGSPositiveDegreeHausdorffDimension
import RequestProject.Section31.EIGSPositiveDegreeDiameterHausdorffDimension
import RequestProject.Section31.EIGSTwoColourPositiveDegreeData
import RequestProject.Section31.EIGSTwoColourActualSpectralParameters

/-! Standard Hausdorff dimension of the unchanged nonprimitive Figure 3
model, in both actual native and diameter-normalized metrics. Candidate. -/

namespace EIGS
open MeasureTheory Filter Topology IGS.Sec31
open scoped Classical ENNReal NNReal
noncomputable section
set_option maxHeartbeats 12000000

theorem twoColourSystem_native_hausdorff_dimension :
    let parameters := xiPathMetricDataOfRules twoColourSystem twoColourSystem_connected twoColourSystem_loopless twoColourSystem_edgesUnique twoColourSystem_distancePositive
    let mass := xiMassParametersOfRules twoColourSystem twoColourSystem_connected twoColourSystem_distancePositive
    dimH (Set.univ : Set parameters.LimitSpace) =
      ENNReal.ofReal (Real.log (3 + Real.sqrt 6) / Real.log 2) := by
  have actual := xiCompletion_hausdorff_dimension_of_rules_of_positive_degree_data twoColourSystem twoColourSystem_connected
    twoColourSystem_loopless twoColourSystem_edgesUnique twoColourSystem_plantingNonadjacent
    twoColourSystem_distancePositive twoColourPositiveDegreeData
  have actualExponent :
      Real.log (xiMassParametersOfRules twoColourSystem twoColourSystem_connected
        twoColourSystem_distancePositive).rate /
        Real.log (twoColourSystem.distanceSpectralRadius twoColourSystem_connected) =
      Real.log (3 + Real.sqrt 6) / Real.log 2 := by
    rw [XiMassParameters.rate_eq_spectralRadius, twoColourSystem_massSpectralRadius,
      twoColourSystem_distanceSpectralRadius]
  simpa only [actualExponent] using actual

theorem twoColourSystem_diameter_hausdorff_dimension :
    let parameters := xiPathMetricDataOfRules twoColourSystem twoColourSystem_connected twoColourSystem_loopless twoColourSystem_edgesUnique twoColourSystem_distancePositive
    let distanceGreaterThanOne : 1 < twoColourSystem.distanceSpectralRadius twoColourSystem_connected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (twoColourSystem.two_le_distanceSpectralRadius twoColourSystem_connected twoColourSystem_edgesUnique twoColourSystem_plantingNonadjacent twoColourSystem_distancePositive)
    let mass := xiMassParametersOfRules twoColourSystem twoColourSystem_connected twoColourSystem_distancePositive
    let normalizedMetric := MeasuredGHP.xiCompletionDiameterMetricSpace twoColourSystem twoColourSystem_connected parameters.lengths
      parameters.lengthsPositive (twoColourSystem.distanceSpectralRadius twoColourSystem_connected) distanceGreaterThanOne parameters.eigenpair
    @dimH parameters.LimitSpace (@MetricSpace.toEMetricSpace parameters.LimitSpace normalizedMetric)
      (Set.univ : Set parameters.LimitSpace) =
        ENNReal.ofReal (Real.log (3 + Real.sqrt 6) / Real.log 2) := by
  have actual := xiDiameterCompletion_hausdorff_dimension_of_rules_of_positive_degree_data twoColourSystem twoColourSystem_connected
    twoColourSystem_loopless twoColourSystem_edgesUnique twoColourSystem_plantingNonadjacent
    twoColourSystem_distancePositive twoColourPositiveDegreeData
  have actualExponent :
      Real.log (xiMassParametersOfRules twoColourSystem twoColourSystem_connected
        twoColourSystem_distancePositive).rate /
        Real.log (twoColourSystem.distanceSpectralRadius twoColourSystem_connected) =
      Real.log (3 + Real.sqrt 6) / Real.log 2 := by
    rw [XiMassParameters.rate_eq_spectralRadius, twoColourSystem_massSpectralRadius,
      twoColourSystem_distanceSpectralRadius]
  simpa only [actualExponent] using actual

end
end EIGS

#print axioms EIGS.twoColourSystem_native_hausdorff_dimension
#print axioms EIGS.twoColourSystem_diameter_hausdorff_dimension

