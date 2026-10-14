import RequestProject.Section31.CompactRealCoveringNumberPowerBounds
import RequestProject.Section3.SpectralDimension

/-! The genuine standard covering-number logarithmic limit. Uniform lower
volume and almost-everywhere logarithmic upper volume supply every input. -/

namespace IGS.Sec31
open MeasureTheory Filter Topology
noncomputable section

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]

theorem compact_coveringNumber_logarithmic_limit_of_ball_mass_bounds
    (physicalMeasure : Measure Space) [IsProbabilityMeasure physicalMeasure]
    (exponent logExponent massConstant radiusThreshold : ℝ)
    (logExponentNonnegative : 0 ≤ logExponent)
    (massConstantPositive : 0 < massConstant) (radiusThresholdPositive : 0 < radiusThreshold)
    (ballMassLower : ∀ point : Space, ∀ radius : ℝ, 0 < radius → radius ≤ radiusThreshold →
      massConstant * radius ^ exponent ≤ physicalMeasure.real (Metric.ball point radius))
    (ballMassUpper : ∀ᵐ point ∂physicalMeasure, ∃ coefficient threshold : ℝ,
      0 < coefficient ∧ 0 < threshold ∧ ∀ radius : ℝ, 0 < radius → radius ≤ threshold →
        physicalMeasure.real (Metric.ball point radius) ≤
          coefficient * (radius ^ exponent * |Real.log radius| ^ logExponent)) :
    Tendsto (fun radius : ℝ => Real.log (realCoveringNumber Space radius) / (-Real.log radius))
      (𝓝[>] (0 : ℝ)) (𝓝 exponent) := by
  obtain ⟨upperConstant, upperThreshold, upperPositive, upperThresholdPositive, upperBound⟩ :=
    compact_realCoveringNumber_upper_of_ball_mass_lower physicalMeasure exponent massConstant
      radiusThreshold massConstantPositive radiusThresholdPositive ballMassLower
  obtain ⟨lowerConstant, lowerThreshold, lowerPositive, lowerThresholdPositive, lowerBound⟩ :=
    compact_realCoveringNumber_lower_of_ae_ball_mass_upper physicalMeasure exponent logExponent
      logExponentNonnegative ballMassUpper
  have logarithmic := IGS.tendsto_spectral_dimension_of_bounds
    (realCoveringNumber Space) exponent logExponent lowerConstant upperConstant
    (min lowerThreshold upperThreshold) lowerPositive upperPositive
    (lt_min lowerThresholdPositive upperThresholdPositive)
    (fun radius membership => lowerBound radius membership.1 (membership.2.le.trans (min_le_left _ _)))
    (fun radius membership => upperBound radius membership.1 (membership.2.le.trans (min_le_right _ _)))
  have scaled := logarithmic.const_mul (1 / 2 : ℝ)
  convert scaled using 1
  · funext radius
    ring
  · ring

end
end IGS.Sec31

#print axioms IGS.Sec31.compact_coveringNumber_logarithmic_limit_of_ball_mass_bounds
