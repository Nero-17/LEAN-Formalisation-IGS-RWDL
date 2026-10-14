import RequestProject.Section31.EIGSFiniteBornBallMassOfRules
import RequestProject.Section31.BallMassDiameterScaling
import RequestProject.Section31.EIGSOriginalCountableRealisation

/-! Finite-born two-sided physical ball volume in the manuscript's
diameter-normalized completion. The same finite vertex embedding and
physical limiting measure are retained. -/

namespace EIGS
open MeasureTheory Metric
open scoped Classical
noncomputable section
variable {K : ℕ}

theorem exists_xiFiniteBornDiameterBallMass_of_rules (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (primitiveDegree : (degreeMatrix system).IsPrimitive) :
    let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system connected distancePositive
    let normalizedMetric := MeasuredGHP.xiCompletionDiameterMetricSpace system connected parameters.lengths
      parameters.lengthsPositive (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair
    ∀ birth (vertex : XiVtx system birth), ∃ lower upper threshold : ℝ,
      0 < lower ∧ 0 < upper ∧ 0 < threshold ∧ ∀ radius : ℝ,
      0 < radius → radius ≤ threshold →
      lower * radius ^ ((Real.log mass.rate -
        Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system))) /
        Real.log (system.distanceSpectralRadius connected)) ≤
        (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass).real
          (@Metric.ball parameters.LimitSpace normalizedMetric.toPseudoMetricSpace
            (parameters.vertexEmbedding birth vertex) radius) ∧
      (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass).real
          (@Metric.ball parameters.LimitSpace normalizedMetric.toPseudoMetricSpace
            (parameters.vertexEmbedding birth vertex) radius) ≤
        upper * radius ^ ((Real.log mass.rate -
          Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system))) /
          Real.log (system.distanceSpectralRadius connected)) := by
  intro parameters distanceGreaterThanOne mass normalizedMetric
  let diameter := xiCompletionDiameter system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) (zero_lt_one.trans distanceGreaterThanOne) parameters.eigenpair
  have diameterPositive : 0 < diameter := xiCompletionDiameter_positive system connected parameters.lengths
    parameters.lengthsPositive (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair
  let exponent := (Real.log mass.rate - Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system))) /
    Real.log (system.distanceSpectralRadius connected)
  let nativeMetric : MetricSpace parameters.LimitSpace := xiCompletionMetricSpace system connected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected)
    (zero_lt_one.trans distanceGreaterThanOne) parameters.eigenpair
  have ballIdentity (point : parameters.LimitSpace) (radius : ℝ) :
      @Metric.ball parameters.LimitSpace normalizedMetric.toPseudoMetricSpace point radius =
        @Metric.ball parameters.LimitSpace nativeMetric.toPseudoMetricSpace point (diameter * radius) :=
    @MeasuredGHP.diameterNormalized_ball_eq_native parameters.LimitSpace nativeMetric diameterPositive point radius
  have native := exists_xiFiniteBornBallMass_of_rules system connected loopless unique
    plantingNonadjacent distancePositive primitiveDegree
  intro birth vertex
  obtain ⟨lower, upper, threshold, lowerPositive, upperPositive, thresholdPositive, nativeBound⟩ := native birth vertex
  refine ⟨lower * diameter ^ exponent, upper * diameter ^ exponent, threshold / diameter,
    mul_pos lowerPositive (Real.rpow_pos_of_pos diameterPositive _),
    mul_pos upperPositive (Real.rpow_pos_of_pos diameterPositive _),
    div_pos thresholdPositive diameterPositive, ?_⟩
  intro radius radiusPositive radiusSmall
  have nativeSmall : diameter * radius ≤ threshold := by
    simpa only [mul_comm] using (le_div_iff₀ diameterPositive).mp radiusSmall
  have result := nativeBound (diameter * radius) (mul_pos diameterPositive radiusPositive) nativeSmall
  rw [ballIdentity]
  simpa only [Real.mul_rpow diameterPositive.le radiusPositive.le, mul_assoc] using result

end
end EIGS

#print axioms EIGS.exists_xiFiniteBornDiameterBallMass_of_rules
