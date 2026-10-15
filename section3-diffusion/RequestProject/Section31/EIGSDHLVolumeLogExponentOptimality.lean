import RequestProject.Section31.EIGSDHLLogarithmicVolumeFluctuation
import RequestProject.Section31.LogarithmicVolumeExponentOptimality

/-! For the actual DHL measure in its original diameter-normalized metric,
no logarithmic upper volume exponent below one can hold at almost any point,
regardless of the positive upper coefficient or the small-radius cutoff.
This is volume optimality and makes no heat-kernel optimality claim. -/

namespace EIGS
open MeasureTheory IGS.Sec31
noncomputable section

theorem dhl_actual_diameter_volume_log_exponent_optimal
    (exponent : ℝ) (exponentBelowOne : exponent < 1) :
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
      ∀ upper : ℝ, 0 < upper → ∀ radiusThreshold : ℝ, 0 < radiusThreshold →
        ∃ radius : ℝ, 0 < radius ∧ radius < radiusThreshold ∧
          upper * |Real.log radius| ^ exponent * radius ^ 2 <
            (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
              (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass).real
              (@Metric.ball parameters.LimitSpace normalizedMetric.toPseudoMetricSpace point radius) := by
  intro system connected parameters distanceGreaterThanOne mass normalizedMetric
  have epsilonPositive : 0 < (1 - exponent) / 2 :=
    div_pos (sub_pos.mpr exponentBelowOne) (by norm_num)
  filter_upwards [dhl_actual_diameter_logarithmic_volume_fluctuation
    ((1 - exponent) / 2) epsilonPositive] with point lowerAtPoint
  obtain ⟨lower, lowerPositive, arbitrarilySmall⟩ := lowerAtPoint
  exact logarithmic_volume_lower_excludes_smaller_exponent
    (fun radius => (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass).real
      (@Metric.ball parameters.LimitSpace normalizedMetric.toPseudoMetricSpace point radius))
      exponent exponentBelowOne lower lowerPositive arbitrarilySmall

end
end EIGS

#print axioms EIGS.dhl_actual_diameter_volume_log_exponent_optimal
