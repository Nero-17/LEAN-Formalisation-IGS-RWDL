import RequestProject.Section31.EIGSDHLLogarithmicVolumeFluctuation
import RequestProject.Section31.CommonAELogarithmicVolumeLower

/-! A single full-measure set for the actual DHL measure in its original
diameter-normalized metric carries all positive-epsilon volume lower bounds
and excludes every logarithmic volume-upper exponent below one. -/

namespace EIGS
open MeasureTheory IGS.Sec31
noncomputable section

theorem dhl_actual_diameter_common_ae_volume_optimality :
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
      (∀ epsilon : ℝ, 0 < epsilon → ∃ lower : ℝ, 0 < lower ∧
        ∀ radiusThreshold : ℝ, 0 < radiusThreshold → ∃ radius : ℝ,
          0 < radius ∧ radius < radiusThreshold ∧
          lower * |Real.log radius| ^ (1 - epsilon) * radius ^ 2 ≤
            (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
              (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass).real
              (@Metric.ball parameters.LimitSpace normalizedMetric.toPseudoMetricSpace point radius)) ∧
      (∀ exponent : ℝ, exponent < 1 → ∀ upper : ℝ, 0 < upper →
        ∀ radiusThreshold : ℝ, 0 < radiusThreshold → ∃ radius : ℝ,
          0 < radius ∧ radius < radiusThreshold ∧
          upper * |Real.log radius| ^ exponent * radius ^ 2 <
            (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
              (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass).real
              (@Metric.ball parameters.LimitSpace normalizedMetric.toPseudoMetricSpace point radius)) := by
  intro system connected parameters distanceGreaterThanOne mass normalizedMetric
  let volume := fun point radius =>
    (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass).real
      (@Metric.ball parameters.LimitSpace normalizedMetric.toPseudoMetricSpace point radius)
  have common := ae_all_logarithmic_volume_lower
    (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass)
    volume (fun epsilon epsilonPositive =>
      dhl_actual_diameter_logarithmic_volume_fluctuation epsilon epsilonPositive)
  filter_upwards [common] with point allEpsilons
  refine ⟨allEpsilons, ?_⟩
  intro exponent exponentBelowOne
  have epsilonPositive : 0 < (1 - exponent) / 2 :=
    div_pos (sub_pos.mpr exponentBelowOne) (by norm_num)
  obtain ⟨lower, lowerPositive, arbitrarilySmall⟩ :=
    allEpsilons ((1 - exponent) / 2) epsilonPositive
  exact logarithmic_volume_lower_excludes_smaller_exponent
    (volume point) exponent exponentBelowOne lower lowerPositive arbitrarilySmall

end
end EIGS

#print axioms EIGS.dhl_actual_diameter_common_ae_volume_optimality
