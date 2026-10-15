import RequestProject.Section31.EIGSDHLInfiniteGeometricVolumeLower
import RequestProject.Section31.InfiniteGeometricLogarithmicVolumeLower
import RequestProject.Section31.EIGSOriginalCountableRealisation
import RequestProject.Section31.EIGSMetricOfRules

/-! The manuscript's actual DHL volume-fluctuation assertion, with its
original diameter-normalized completion metric and actual limit measure.
Every epsilon is allowed, and radii occur below every positive cutoff.
No probabilistic, volume, or metric-dimension conclusion is an assumption. -/

namespace EIGS
open MeasureTheory Metric IGS.Sec31
noncomputable section

theorem dhl_actual_diameter_logarithmic_volume_fluctuation (epsilon : ℝ) (epsilonPositive : 0 < epsilon) :
    let system := flowerSystem 2 2
    let connected := flowerSystem_connected 2 2 (by norm_num) (by norm_num)
    let parameters := xiPathMetricDataOfRules system connected
      (flowerSystem_loopless 2 2) (flowerSystem_edgesUnique 2 2 (by norm_num))
      (flowerSystem_distancePositive 2 2)
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius connected (flowerSystem_edgesUnique 2 2 (by norm_num))
          (flowerSystem_plantingNonadjacent 2 2 (by norm_num)) (flowerSystem_distancePositive 2 2))
    let mass := xiMassParametersOfRules system connected (flowerSystem_distancePositive 2 2)
    let normalizedMetric := MeasuredGHP.xiCompletionDiameterMetricSpace system connected parameters.lengths
      parameters.lengthsPositive (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair
    ∀ᵐ point ∂xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass,
      ∃ lower : ℝ, 0 < lower ∧ ∀ radiusThreshold : ℝ, 0 < radiusThreshold →
        ∃ radius : ℝ, 0 < radius ∧ radius < radiusThreshold ∧
          lower * |Real.log radius| ^ (1 - epsilon) * radius ^ 2 ≤
            (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
              (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass).real
              (@Metric.ball parameters.LimitSpace normalizedMetric.toPseudoMetricSpace point radius) := by
  intro system connected parameters distanceGreaterThanOne mass normalizedMetric
  let diameter := xiCompletionDiameter system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) (zero_lt_one.trans distanceGreaterThanOne) parameters.eigenpair
  have diameterPositive : 0 < diameter := xiCompletionDiameter_positive system connected parameters.lengths
    parameters.lengthsPositive (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair
  let nativeMetric : MetricSpace parameters.LimitSpace := xiCompletionMetricSpace system connected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected)
    (zero_lt_one.trans distanceGreaterThanOne) parameters.eigenpair
  have distanceIdentity : system.distanceSpectralRadius connected = 2 := by
    simpa only [system, connected] using flowerSystem_distanceSpectralRadius 2 2 (by norm_num) (by norm_num)
  obtain ⟨coefficient, radiusFactor, coefficientPositive, radiusPositive, geometric⟩ :=
    exists_dhl_ae_infinite_geometric_volume_lower connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass
  let smallerEpsilon := min epsilon (1 / 2 : ℝ)
  have smallerPositive : 0 < smallerEpsilon := lt_min epsilonPositive (by norm_num)
  have smallerBelowOne : smallerEpsilon < 1 := (min_le_right _ _).trans_lt (by norm_num)
  filter_upwards [geometric smallerEpsilon smallerPositive smallerBelowOne] with point infiniteScales
  have ballIdentity (radius : ℝ) :
      @Metric.ball parameters.LimitSpace normalizedMetric.toPseudoMetricSpace point radius =
        @Metric.ball parameters.LimitSpace nativeMetric.toPseudoMetricSpace point (diameter * radius) :=
    @MeasuredGHP.diameterNormalized_ball_eq_native parameters.LimitSpace nativeMetric diameterPositive point radius
  have normalizedScales : ∀ threshold : ℕ, ∃ level : ℕ, threshold ≤ level ∧
      coefficient * (level : ℝ) ^ (1 - smallerEpsilon) / (4 : ℝ) ^ level ≤
        (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass).real
          (@Metric.ball parameters.LimitSpace normalizedMetric.toPseudoMetricSpace point
            ((radiusFactor / diameter) * (2 : ℝ)⁻¹ ^ level)) := by
    intro threshold
    obtain ⟨level, large, lower⟩ := infiniteScales threshold
    refine ⟨level, large, ?_⟩
    have radiusIdentity : diameter * ((radiusFactor / diameter) * (2 : ℝ)⁻¹ ^ level) =
        radiusFactor * (system.distanceSpectralRadius connected)⁻¹ ^ level := by
      rw [distanceIdentity]
      field_simp [diameterPositive.ne']
    rw [ballIdentity, radiusIdentity]
    exact lower
  obtain ⟨lower, lowerPositive, arbitrarilySmall⟩ := infinite_geometric_volume_lower_logarithmic
    (fun radius => (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass).real
      (@Metric.ball parameters.LimitSpace normalizedMetric.toPseudoMetricSpace point radius))
    coefficient (radiusFactor / diameter) smallerEpsilon coefficientPositive
      (div_pos radiusPositive diameterPositive) smallerPositive smallerBelowOne normalizedScales
  refine ⟨lower, lowerPositive, ?_⟩
  intro radiusThreshold thresholdPositive
  obtain ⟨radius, positive, small, volumeLower⟩ := arbitrarilySmall
    (min radiusThreshold (Real.exp (-1))) (lt_min thresholdPositive (Real.exp_pos _))
  have logSmall : Real.log radius ≤ -1 := by
    have comparison := Real.log_le_log positive (small.le.trans (min_le_right _ _))
    simpa only [Real.log_exp] using comparison
  have logMagnitude : 1 ≤ |Real.log radius| := by
    rw [abs_of_nonpos (by linarith : Real.log radius ≤ 0)]
    linarith
  have profile := Real.rpow_le_rpow_of_exponent_le logMagnitude
    (sub_le_sub_left (show smallerEpsilon ≤ epsilon from min_le_left _ _) 1)
  exact ⟨radius, positive, small.trans_le (min_le_left _ _),
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left profile lowerPositive.le)
      (sq_nonneg radius)).trans volumeLower⟩

end
end EIGS

#print axioms EIGS.dhl_actual_diameter_logarithmic_volume_fluctuation
