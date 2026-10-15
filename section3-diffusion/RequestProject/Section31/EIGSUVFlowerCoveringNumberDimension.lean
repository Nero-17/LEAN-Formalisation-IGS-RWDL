import RequestProject.Section31.EIGSDiameterCoveringNumberDimensionOfRules
import RequestProject.Section31.EIGSUVFlowerDistanceSpectrum
import RequestProject.Section31.EIGSUVFlowerDegreeSpectrum
import RequestProject.Section31.EIGSUVFlowerMassSpectrum

/-! Actual standard covering-number limits for the genuine unequal-path flower completion, in
both native and manuscript diameter-normalized metrics. -/

namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical
noncomputable section
set_option maxHeartbeats 12000000

theorem uvFlowerSystem_native_coveringNumber_dimension (firstLength secondLength : ℕ)
    (firstLengthAtLeastTwo : 2 ≤ firstLength) (secondLengthAtLeastTwo : 2 ≤ secondLength) :
    let parameters := xiPathMetricDataOfRules (uvFlowerSystem firstLength secondLength) (uvFlowerSystem_connected firstLength secondLength (by omega) (by omega)) (uvFlowerSystem_loopless firstLength secondLength) (uvFlowerSystem_edgesUnique firstLength secondLength firstLengthAtLeastTwo secondLengthAtLeastTwo) (uvFlowerSystem_distancePositive firstLength secondLength)
    let mass := xiMassParametersOfRules (uvFlowerSystem firstLength secondLength) (uvFlowerSystem_connected firstLength secondLength (by omega) (by omega)) (uvFlowerSystem_distancePositive firstLength secondLength)
    Tendsto (fun radius : ℝ => Real.log (realCoveringNumber parameters.LimitSpace radius) / (-Real.log radius))
      (𝓝[>] (0 : ℝ))
      (𝓝 (Real.log ((firstLength : ℝ) + secondLength) / Real.log (min firstLength secondLength : ℕ))) := by
  have actual := xiCompletion_coveringNumber_dimension_of_rules (uvFlowerSystem firstLength secondLength)
    (uvFlowerSystem_connected firstLength secondLength (by omega) (by omega))
    (uvFlowerSystem_loopless firstLength secondLength)
    (uvFlowerSystem_edgesUnique firstLength secondLength firstLengthAtLeastTwo secondLengthAtLeastTwo)
    (uvFlowerSystem_plantingNonadjacent firstLength secondLength firstLengthAtLeastTwo secondLengthAtLeastTwo)
    (uvFlowerSystem_distancePositive firstLength secondLength)
    (uvFlowerSystem_degreeMatrix_primitive firstLength secondLength (by omega) (by omega))
  have actualExponent :
      Real.log (xiMassParametersOfRules (uvFlowerSystem firstLength secondLength)
        (uvFlowerSystem_connected firstLength secondLength (by omega) (by omega))
        (uvFlowerSystem_distancePositive firstLength secondLength)).rate /
        Real.log ((uvFlowerSystem firstLength secondLength).distanceSpectralRadius
          (uvFlowerSystem_connected firstLength secondLength (by omega) (by omega))) =
        Real.log ((firstLength : ℝ) + secondLength) / Real.log (min firstLength secondLength : ℕ) := by
    rw [XiMassParameters.rate_eq_spectralRadius, uvFlowerSystem_massSpectralRadius,
      uvFlowerSystem_distanceSpectralRadius firstLength secondLength (by omega) secondLengthAtLeastTwo]
  simpa only [actualExponent] using actual

theorem uvFlowerSystem_diameter_coveringNumber_dimension (firstLength secondLength : ℕ)
    (firstLengthAtLeastTwo : 2 ≤ firstLength) (secondLengthAtLeastTwo : 2 ≤ secondLength) :
    let parameters := xiPathMetricDataOfRules (uvFlowerSystem firstLength secondLength) (uvFlowerSystem_connected firstLength secondLength (by omega) (by omega)) (uvFlowerSystem_loopless firstLength secondLength) (uvFlowerSystem_edgesUnique firstLength secondLength firstLengthAtLeastTwo secondLengthAtLeastTwo) (uvFlowerSystem_distancePositive firstLength secondLength)
    let distanceGreaterThanOne : 1 < (uvFlowerSystem firstLength secondLength).distanceSpectralRadius (uvFlowerSystem_connected firstLength secondLength (by omega) (by omega)) :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        ((uvFlowerSystem firstLength secondLength).two_le_distanceSpectralRadius (uvFlowerSystem_connected firstLength secondLength (by omega) (by omega)) (uvFlowerSystem_edgesUnique firstLength secondLength firstLengthAtLeastTwo secondLengthAtLeastTwo) (uvFlowerSystem_plantingNonadjacent firstLength secondLength firstLengthAtLeastTwo secondLengthAtLeastTwo) (uvFlowerSystem_distancePositive firstLength secondLength))
    let mass := xiMassParametersOfRules (uvFlowerSystem firstLength secondLength) (uvFlowerSystem_connected firstLength secondLength (by omega) (by omega)) (uvFlowerSystem_distancePositive firstLength secondLength)
    let normalizedMetric := MeasuredGHP.xiCompletionDiameterMetricSpace (uvFlowerSystem firstLength secondLength) (uvFlowerSystem_connected firstLength secondLength (by omega) (by omega)) parameters.lengths
      parameters.lengthsPositive ((uvFlowerSystem firstLength secondLength).distanceSpectralRadius (uvFlowerSystem_connected firstLength secondLength (by omega) (by omega))) distanceGreaterThanOne parameters.eigenpair
    Tendsto (fun radius : ℝ =>
      Real.log (@realCoveringNumber parameters.LimitSpace normalizedMetric radius) / (-Real.log radius))
      (𝓝[>] (0 : ℝ))
      (𝓝 (Real.log ((firstLength : ℝ) + secondLength) / Real.log (min firstLength secondLength : ℕ))) := by
  have actual := xiDiameterCompletion_coveringNumber_dimension_of_rules (uvFlowerSystem firstLength secondLength)
    (uvFlowerSystem_connected firstLength secondLength (by omega) (by omega))
    (uvFlowerSystem_loopless firstLength secondLength)
    (uvFlowerSystem_edgesUnique firstLength secondLength firstLengthAtLeastTwo secondLengthAtLeastTwo)
    (uvFlowerSystem_plantingNonadjacent firstLength secondLength firstLengthAtLeastTwo secondLengthAtLeastTwo)
    (uvFlowerSystem_distancePositive firstLength secondLength)
    (uvFlowerSystem_degreeMatrix_primitive firstLength secondLength (by omega) (by omega))
  have actualExponent :
      Real.log (xiMassParametersOfRules (uvFlowerSystem firstLength secondLength)
        (uvFlowerSystem_connected firstLength secondLength (by omega) (by omega))
        (uvFlowerSystem_distancePositive firstLength secondLength)).rate /
        Real.log ((uvFlowerSystem firstLength secondLength).distanceSpectralRadius
          (uvFlowerSystem_connected firstLength secondLength (by omega) (by omega))) =
        Real.log ((firstLength : ℝ) + secondLength) / Real.log (min firstLength secondLength : ℕ) := by
    rw [XiMassParameters.rate_eq_spectralRadius, uvFlowerSystem_massSpectralRadius,
      uvFlowerSystem_distanceSpectralRadius firstLength secondLength (by omega) secondLengthAtLeastTwo]
  simpa only [actualExponent] using actual

end
end EIGS

#print axioms EIGS.uvFlowerSystem_native_coveringNumber_dimension
#print axioms EIGS.uvFlowerSystem_diameter_coveringNumber_dimension

