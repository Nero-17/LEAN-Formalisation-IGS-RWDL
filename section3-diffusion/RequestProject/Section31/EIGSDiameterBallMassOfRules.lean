import RequestProject.Section31.EIGSAllPointBallMassLowerOfRules
import RequestProject.Section31.EIGSTypicalBallMassUpperAllRadiiOfRules
import RequestProject.Section31.BallMassDiameterScaling
import RequestProject.Section31.EIGSOriginalCountableRealisation

/-! Typical-point manuscript ball volumes in the explicitly specified
diameter-normalized completion metric. All native-volume inputs are
proved actual-model consumers, and positive metric scaling is internal. -/

namespace EIGS
open MeasureTheory Metric IGS.Sec31
open scoped Classical
noncomputable section
set_option maxHeartbeats 6000000
variable {K : ℕ}
variable (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (primitiveDegree : (degreeMatrix system).IsPrimitive)
include connected loopless unique plantingNonadjacent distancePositive primitiveDegree

theorem xiTypicalDiameterBallMass_of_rules (epsilon : ℝ) (epsilonPositive : 0 < epsilon) :
    let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system connected distancePositive
    let normalizedMetric := MeasuredGHP.xiCompletionDiameterMetricSpace system connected parameters.lengths
      parameters.lengthsPositive (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair
    ∀ᵐ point ∂xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass,
      ∃ lower upper threshold : ℝ, 0 < lower ∧ 0 < upper ∧ 0 < threshold ∧
      ∀ radius : ℝ, 0 < radius → radius ≤ threshold →
      lower * radius ^ (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected)) ≤
        (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass).real
          (@Metric.ball parameters.LimitSpace normalizedMetric.toPseudoMetricSpace point radius) ∧
      (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass).real
          (@Metric.ball parameters.LimitSpace normalizedMetric.toPseudoMetricSpace point radius) ≤
        upper * radius ^ (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected)) *
          |Real.log radius| ^
            (1 / (Real.log mass.rate / Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)) - 1) + epsilon) := by
  intro parameters distanceGreaterThanOne mass normalizedMetric
  let physicalMeasure := xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass
  let diameter := xiCompletionDiameter system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) (zero_lt_one.trans distanceGreaterThanOne) parameters.eigenpair
  have diameterPositive : 0 < diameter := xiCompletionDiameter_positive system connected parameters.lengths
    parameters.lengthsPositive (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair
  let nativeMetric : MetricSpace parameters.LimitSpace := xiCompletionMetricSpace system connected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected)
    (zero_lt_one.trans distanceGreaterThanOne) parameters.eigenpair
  have ballIdentity (point : parameters.LimitSpace) (radius : ℝ) :
      @Metric.ball parameters.LimitSpace normalizedMetric.toPseudoMetricSpace point radius =
        @Metric.ball parameters.LimitSpace nativeMetric.toPseudoMetricSpace point (diameter * radius) :=
    @MeasuredGHP.diameterNormalized_ball_eq_native parameters.LimitSpace nativeMetric diameterPositive point radius
  let exponent := Real.log mass.rate / Real.log (system.distanceSpectralRadius connected)
  let logExponent := 1 / (Real.log mass.rate /
    Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)) - 1) + epsilon
  have degreeGreaterThanOne := degree_spectralRadius_gt_one_of_primitive system primitiveDegree
  have degreeMass : finiteRealMatrixSpectralRadius (degreeMatrix system) < mass.rate := by
    rw [XiMassParameters.rate_eq_spectralRadius system mass]
    exact degree_spectralRadius_lt_mass_of_primitive system connected loopless
      plantingNonadjacent distancePositive primitiveDegree
  have degreeDimensionGreaterThanOne : 1 < Real.log mass.rate /
      Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)) :=
    (one_lt_div (Real.log_pos degreeGreaterThanOne)).mpr
      (Real.log_lt_log (zero_lt_one.trans degreeGreaterThanOne) degreeMass)
  have logExponentNonnegative : 0 ≤ logExponent := by
    dsimp only [logExponent]
    exact add_nonneg (div_nonneg zero_le_one (sub_pos.mpr degreeDimensionGreaterThanOne).le) epsilonPositive.le
  obtain ⟨nativeLower, nativeLowerThreshold, nativeLowerPositive, nativeLowerThresholdPositive, lowerNative⟩ :=
    exists_xiAllPointBallMassLower_of_rules system connected loopless unique plantingNonadjacent
      distancePositive primitiveDegree
  have upperNative := xiTypicalBallMassUpperAllRadii_of_rules system connected loopless unique
    plantingNonadjacent distancePositive primitiveDegree epsilon epsilonPositive
  filter_upwards [upperNative] with point bound
  obtain ⟨nativeUpper, nativeUpperThreshold, nativeUpperPositive, nativeUpperThresholdPositive, upperAtPoint⟩ := bound
  obtain ⟨lower, lowerThreshold, lowerPositive, lowerThresholdPositive, scaledLower⟩ :=
    local_power_volume_lower_positive_scaling
      (fun radius => physicalMeasure.real (@Metric.ball parameters.LimitSpace nativeMetric.toPseudoMetricSpace point radius))
      diameter exponent nativeLower nativeLowerThreshold diameterPositive nativeLowerPositive
      nativeLowerThresholdPositive (lowerNative point)
  obtain ⟨upper, upperThreshold, upperPositive, upperThresholdPositive, scaledUpper⟩ :=
    local_logarithmic_volume_upper_positive_scaling
      (fun radius => physicalMeasure.real (@Metric.ball parameters.LimitSpace nativeMetric.toPseudoMetricSpace point radius))
      diameter exponent logExponent nativeUpper nativeUpperThreshold diameterPositive logExponentNonnegative
      nativeUpperPositive nativeUpperThresholdPositive upperAtPoint
  refine ⟨lower, upper, min lowerThreshold upperThreshold, lowerPositive, upperPositive,
    lt_min lowerThresholdPositive upperThresholdPositive, ?_⟩
  intro radius radiusPositive radiusSmall
  rw [ballIdentity]
  exact ⟨scaledLower radius radiusPositive (radiusSmall.trans (min_le_left _ _)),
    scaledUpper radius radiusPositive (radiusSmall.trans (min_le_right _ _))⟩

end
end EIGS

#print axioms EIGS.xiTypicalDiameterBallMass_of_rules
