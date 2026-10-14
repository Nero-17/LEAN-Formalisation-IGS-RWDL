import RequestProject.Section31.EIGSDiameterCoveringNumberDimensionOfRules
import RequestProject.Section31.EIGSPositiveDegreeCoveringDimension
import RequestProject.Section31.EIGSPositiveDegreeDiameterBallMass

/-! Actual volume and covering dimension from positive degree spectral data.
Both native and diameter-normalized metrics retain their original definitions.
Candidate source; no compilation is claimed. -/

namespace EIGS
open MeasureTheory Filter Topology IGS.Sec31
open scoped Classical
noncomputable section
set_option maxHeartbeats 6000000
variable {K : ℕ}

theorem xiDiameterCompletion_coveringNumber_dimension_of_rules_of_positive_degree_data (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (degreeData : XiPositiveDegreeSpectralData system) :
    let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system connected distancePositive
    let normalizedMetric := MeasuredGHP.xiCompletionDiameterMetricSpace system connected parameters.lengths
      parameters.lengthsPositive (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair
    Tendsto (fun radius : ℝ =>
      Real.log (@realCoveringNumber parameters.LimitSpace normalizedMetric radius) / (-Real.log radius))
      (𝓝[>] (0 : ℝ))
      (𝓝 (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected))) := by
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
  obtain ⟨massConstant, radiusThreshold, massConstantPositive, radiusThresholdPositive, nativeLower⟩ :=
    exists_xiAllPointBallMassLower_of_rules_of_positive_degree_data system connected loopless unique plantingNonadjacent
      distancePositive degreeData
  have nativeLowerExact (point : parameters.LimitSpace) (radius : ℝ)
      (radiusPositive : 0 < radius) (radiusSmall : radius ≤ radiusThreshold) :
      massConstant * radius ^ (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected)) ≤
        physicalMeasure.real (@Metric.ball parameters.LimitSpace nativeMetric.toPseudoMetricSpace point radius) :=
    nativeLower point radius radiusPositive radiusSmall
  have normalizedUpper := xiTypicalDiameterBallMass_of_rules_of_positive_degree_data system connected loopless unique
    plantingNonadjacent distancePositive degreeData 1 zero_lt_one
  have degreeGreaterThanOne := degreeData.rate_gt_one
  have degreeMass := degree_spectralRadius_lt_mass_of_positive_degree_data system connected loopless
    plantingNonadjacent distancePositive degreeData
  rw [← XiMassParameters.rate_eq_spectralRadius system mass] at degreeMass
  have ratioGreaterThanOne : 1 < Real.log mass.rate /
      Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)) :=
    (one_lt_div (Real.log_pos degreeGreaterThanOne)).mpr
      (Real.log_lt_log (zero_lt_one.trans degreeGreaterThanOne) degreeMass)
  have logExponentNonnegative : 0 ≤
      1 / (Real.log mass.rate / Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)) - 1) + 1 := by
    have denominatorPositive : 0 < Real.log mass.rate /
        Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)) - 1 := by linarith
    positivity
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
      (radiusPositive : 0 < radius) (radiusSmall : radius ≤ radiusThreshold / diameter) :
      (massConstant * diameter ^ (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected))) *
        radius ^ (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected)) ≤
          physicalMeasure.real (Metric.ball point radius) := by
    have multipliedSmall : diameter * radius ≤ radiusThreshold := by
      simpa only [mul_comm] using (le_div_iff₀ diameterPositive).mp radiusSmall
    change _ ≤ physicalMeasure.real (@Metric.ball parameters.LimitSpace normalizedMetric.toPseudoMetricSpace point radius)
    rw [ballIdentity]
    have actual := nativeLowerExact point (diameter * radius) (mul_pos diameterPositive radiusPositive) multipliedSmall
    simpa only [Real.mul_rpow diameterPositive.le radiusPositive.le, mul_assoc] using actual
  apply @compact_coveringNumber_logarithmic_limit_of_ball_mass_bounds parameters.LimitSpace
    normalizedMetric normalizedCompact nativeMeasurable normalizedBorel physicalMeasure
    (xiLimitMeasure_probability system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass)
    (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected))
    (1 / (Real.log mass.rate / Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)) - 1) + 1)
    (massConstant * diameter ^ (Real.log mass.rate / Real.log (system.distanceSpectralRadius connected)))
    (radiusThreshold / diameter) logExponentNonnegative
    (mul_pos massConstantPositive (Real.rpow_pos_of_pos diameterPositive _))
    (div_pos radiusThresholdPositive diameterPositive) normalizedLower
  filter_upwards [normalizedUpper] with point property
  obtain ⟨lower, upper, threshold, lowerPositive, upperPositive, thresholdPositive, bounds⟩ := property
  refine ⟨upper, threshold, upperPositive, thresholdPositive, ?_⟩
  intro radius radiusPositive radiusSmall
  simpa only [mul_assoc] using (bounds radius radiusPositive radiusSmall).2


end
end EIGS

#print axioms EIGS.xiDiameterCompletion_coveringNumber_dimension_of_rules_of_positive_degree_data

