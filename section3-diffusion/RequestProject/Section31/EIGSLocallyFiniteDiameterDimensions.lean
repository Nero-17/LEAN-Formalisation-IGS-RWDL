import RequestProject.Section31.EIGSLocallyFiniteNativeDimensions
import RequestProject.Section31.EIGSOriginalCountableRealisation
import RequestProject.Section31.BallMassDiameterScaling

/-! The same actual covering and Hausdorff dimensions for the manuscript's
diameter-normalized metric. Native power ball bounds are transported by the
exact ball identity; the physical measure is retained. Candidate source. -/

namespace EIGS
open MeasureTheory Filter Topology IGS.Sec31
open scoped Classical ENNReal NNReal
noncomputable section
set_option maxHeartbeats 6000000

theorem locallyFiniteRuleSystem_diameter_dimensions (canonical : Bool) :
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
    let normalizedMetric := MeasuredGHP.xiCompletionDiameterMetricSpace system connected parameters.lengths
      parameters.lengthsPositive (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair
    Tendsto (fun radius : ℝ =>
      Real.log (@realCoveringNumber parameters.LimitSpace normalizedMetric radius) / (-Real.log radius))
      (𝓝[>] (0 : ℝ))
      (𝓝 (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected))) ∧
    @dimH parameters.LimitSpace (@MetricSpace.toEMetricSpace parameters.LimitSpace normalizedMetric)
      (Set.univ : Set parameters.LimitSpace) =
        ENNReal.ofReal (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected)) := by
  intro system connected parameters distanceGreaterThanOne mass normalizedMetric
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
  obtain ⟨lower, lowerThreshold, lowerPositive, lowerThresholdPositive, nativeLower⟩ :=
    locallyFiniteRuleSystem_native_ball_mass_lower canonical
  obtain ⟨upper, upperThreshold, upperPositive, upperThresholdPositive, nativeUpper⟩ :=
    locallyFiniteRuleSystem_native_ball_mass_upper canonical
  have nativeLowerExact (point : parameters.LimitSpace) (radius : ℝ)
      (radiusPositive : 0 < radius) (radiusSmall : radius ≤ lowerThreshold) :
      lower * radius ^ (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected)) ≤
        physicalMeasure.real (@Metric.ball parameters.LimitSpace nativeMetric.toPseudoMetricSpace point radius) :=
    nativeLower point radius radiusPositive radiusSmall
  have nativeUpperExact (point : parameters.LimitSpace) (radius : ℝ)
      (radiusPositive : 0 < radius) (radiusSmall : radius ≤ upperThreshold) :
      physicalMeasure.real (@Metric.ball parameters.LimitSpace nativeMetric.toPseudoMetricSpace point radius) ≤
        upper * radius ^ (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected)) :=
    nativeUpper point radius radiusPositive radiusSmall
  have dimensionNonnegative : 0 ≤ Real.log mass.rate / Real.log (system.distanceSpectralRadius connected) :=
    div_nonneg (Real.log_nonneg ((by norm_num : (1 : ℝ) ≤ 2).trans
      (XiMassParameters.rate_ge_two system connected (locallyFiniteRuleSystem_plantingNonadjacent canonical) mass)))
      (Real.log_nonneg distanceGreaterThanOne.le)
  letI : MetricSpace parameters.LimitSpace := normalizedMetric
  let nativeMeasurable : MeasurableSpace parameters.LimitSpace :=
    @borel parameters.LimitSpace nativeMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI normalizedBorel : @BorelSpace parameters.LimitSpace
      normalizedMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace nativeMeasurable := ⟨rfl⟩
  letI normalizedCompact : @CompactSpace parameters.LimitSpace
      normalizedMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := xiCompletion_compactSpace system connected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected)
    distanceGreaterThanOne parameters.eigenpair
  have normalizedLower (point : parameters.LimitSpace) (radius : ℝ)
      (radiusPositive : 0 < radius) (radiusSmall : radius ≤ lowerThreshold / diameter) :
      (lower * diameter ^ (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected))) *
        radius ^ (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected)) ≤
          physicalMeasure.real (Metric.ball point radius) := by
    have multipliedSmall : diameter * radius ≤ lowerThreshold := by
      simpa only [mul_comm] using (le_div_iff₀ diameterPositive).mp radiusSmall
    change _ ≤ physicalMeasure.real (@Metric.ball parameters.LimitSpace normalizedMetric.toPseudoMetricSpace point radius)
    rw [ballIdentity]
    simpa only [Real.mul_rpow diameterPositive.le radiusPositive.le, mul_assoc] using
      nativeLowerExact point (diameter * radius) (mul_pos diameterPositive radiusPositive) multipliedSmall
  have almostEverywhere : ∀ᵐ point ∂physicalMeasure, ∃ coefficient threshold : ℝ,
      0 < coefficient ∧ 0 < threshold ∧ ∀ radius : ℝ, 0 < radius → radius ≤ threshold →
        physicalMeasure.real (Metric.ball point radius) ≤
          coefficient * radius ^ (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected)) *
            |Real.log radius| ^ (0 : ℝ) := by
    apply Eventually.of_forall
    intro point
    refine ⟨upper * diameter ^ (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected)),
      upperThreshold / diameter, mul_pos upperPositive (Real.rpow_pos_of_pos diameterPositive _),
      div_pos upperThresholdPositive diameterPositive, ?_⟩
    intro radius radiusPositive radiusSmall
    have multipliedSmall : diameter * radius ≤ upperThreshold := by
      simpa only [mul_comm] using (le_div_iff₀ diameterPositive).mp radiusSmall
    change physicalMeasure.real (@Metric.ball parameters.LimitSpace normalizedMetric.toPseudoMetricSpace point radius) ≤ _
    rw [ballIdentity]
    simpa only [Real.mul_rpow diameterPositive.le radiusPositive.le, mul_assoc, Real.rpow_zero, mul_one] using
      nativeUpperExact point (diameter * radius) (mul_pos diameterPositive radiusPositive) multipliedSmall
  constructor
  · exact @compact_coveringNumber_logarithmic_limit_of_ball_mass_bounds parameters.LimitSpace
      normalizedMetric normalizedCompact nativeMeasurable normalizedBorel physicalMeasure
      (xiLimitMeasure_probability system connected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass)
      (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected)) 0
      (lower * diameter ^ (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected)))
      (lowerThreshold / diameter) (by norm_num)
      (mul_pos lowerPositive (Real.rpow_pos_of_pos diameterPositive _))
      (div_pos lowerThresholdPositive diameterPositive) normalizedLower
      (by simpa only [mul_assoc] using almostEverywhere)
  · exact @compact_hausdorff_dimension_eq_of_ball_mass_bounds parameters.LimitSpace
      normalizedMetric normalizedCompact nativeMeasurable normalizedBorel physicalMeasure
      (xiLimitMeasure_probability system connected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass)
      (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected)) 0
      (lower * diameter ^ (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected)))
      (lowerThreshold / diameter) dimensionNonnegative
      (mul_pos lowerPositive (Real.rpow_pos_of_pos diameterPositive _))
      (div_pos lowerThresholdPositive diameterPositive) normalizedLower almostEverywhere

end
end EIGS

#print axioms EIGS.locallyFiniteRuleSystem_diameter_dimensions
