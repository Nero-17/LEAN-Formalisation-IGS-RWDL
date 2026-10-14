import RequestProject.Section31.EIGSDiameterCoveringNumberDimensionOfRules
import RequestProject.Section31.EIGSFlowerWalkDimension
import RequestProject.Section31.EIGSFlowerDegreePrimitive

/-! Actual standard covering-number limits for the flower completion, in
both native and manuscript diameter-normalized metrics. -/

namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical
noncomputable section
set_option maxHeartbeats 12000000

theorem flowerSystem_native_coveringNumber_dimension (branches segments : ℕ)
    (branchesAtLeastTwo : 2 ≤ branches) (segmentsAtLeastTwo : 2 ≤ segments) :
    let parameters := xiPathMetricDataOfRules (flowerSystem branches segments) (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo) (flowerSystem_loopless branches segments) (flowerSystem_edgesUnique branches segments segmentsAtLeastTwo) (flowerSystem_distancePositive branches segments)
    let mass := xiMassParametersOfRules (flowerSystem branches segments) (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo) (flowerSystem_distancePositive branches segments)
    Tendsto (fun radius : ℝ => Real.log (realCoveringNumber parameters.LimitSpace radius) / (-Real.log radius))
      (𝓝[>] (0 : ℝ))
      (𝓝 (1 + Real.log (branches : ℝ) / Real.log (segments : ℝ))) := by
  have actual := xiCompletion_coveringNumber_dimension_of_rules (flowerSystem branches segments)
    (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo)
    (flowerSystem_loopless branches segments)
    (flowerSystem_edgesUnique branches segments segmentsAtLeastTwo)
    (flowerSystem_plantingNonadjacent branches segments segmentsAtLeastTwo)
    (flowerSystem_distancePositive branches segments)
    (flowerSystem_degreeMatrix_primitive branches segments branchesAtLeastTwo segmentsAtLeastTwo)
  have actualExponent :
      Real.log (xiMassParametersOfRules (flowerSystem branches segments)
        (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo)
        (flowerSystem_distancePositive branches segments)).rate /
        Real.log ((flowerSystem branches segments).distanceSpectralRadius
          (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo)) =
        1 + Real.log (branches : ℝ) / Real.log (segments : ℝ) := by
    rw [XiMassParameters.rate_eq_spectralRadius, flowerSystem_massSpectralRadius,
      flowerSystem_distanceSpectralRadius branches segments (by omega) segmentsAtLeastTwo]
    exact (flower_dims branches segments branchesAtLeastTwo segmentsAtLeastTwo).1
  simpa only [actualExponent] using actual

theorem flowerSystem_diameter_coveringNumber_dimension (branches segments : ℕ)
    (branchesAtLeastTwo : 2 ≤ branches) (segmentsAtLeastTwo : 2 ≤ segments) :
    let parameters := xiPathMetricDataOfRules (flowerSystem branches segments) (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo) (flowerSystem_loopless branches segments) (flowerSystem_edgesUnique branches segments segmentsAtLeastTwo) (flowerSystem_distancePositive branches segments)
    let distanceGreaterThanOne : 1 < (flowerSystem branches segments).distanceSpectralRadius (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo) :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        ((flowerSystem branches segments).two_le_distanceSpectralRadius (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo) (flowerSystem_edgesUnique branches segments segmentsAtLeastTwo) (flowerSystem_plantingNonadjacent branches segments segmentsAtLeastTwo) (flowerSystem_distancePositive branches segments))
    let mass := xiMassParametersOfRules (flowerSystem branches segments) (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo) (flowerSystem_distancePositive branches segments)
    let normalizedMetric := MeasuredGHP.xiCompletionDiameterMetricSpace (flowerSystem branches segments) (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo) parameters.lengths
      parameters.lengthsPositive ((flowerSystem branches segments).distanceSpectralRadius (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo)) distanceGreaterThanOne parameters.eigenpair
    Tendsto (fun radius : ℝ =>
      Real.log (@realCoveringNumber parameters.LimitSpace normalizedMetric radius) / (-Real.log radius))
      (𝓝[>] (0 : ℝ))
      (𝓝 (1 + Real.log (branches : ℝ) / Real.log (segments : ℝ))) := by
  have actual := xiDiameterCompletion_coveringNumber_dimension_of_rules (flowerSystem branches segments)
    (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo)
    (flowerSystem_loopless branches segments)
    (flowerSystem_edgesUnique branches segments segmentsAtLeastTwo)
    (flowerSystem_plantingNonadjacent branches segments segmentsAtLeastTwo)
    (flowerSystem_distancePositive branches segments)
    (flowerSystem_degreeMatrix_primitive branches segments branchesAtLeastTwo segmentsAtLeastTwo)
  have actualExponent :
      Real.log (xiMassParametersOfRules (flowerSystem branches segments)
        (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo)
        (flowerSystem_distancePositive branches segments)).rate /
        Real.log ((flowerSystem branches segments).distanceSpectralRadius
          (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo)) =
        1 + Real.log (branches : ℝ) / Real.log (segments : ℝ) := by
    rw [XiMassParameters.rate_eq_spectralRadius, flowerSystem_massSpectralRadius,
      flowerSystem_distanceSpectralRadius branches segments (by omega) segmentsAtLeastTwo]
    exact (flower_dims branches segments branchesAtLeastTwo segmentsAtLeastTwo).1
  simpa only [actualExponent] using actual

end
end EIGS

#print axioms EIGS.flowerSystem_native_coveringNumber_dimension
#print axioms EIGS.flowerSystem_diameter_coveringNumber_dimension
