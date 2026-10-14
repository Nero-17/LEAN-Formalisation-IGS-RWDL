import RequestProject.Section31.EIGSContinuousBallMeanOfRules
import RequestProject.Section31.EIGSNormalizedContinuousBallSurvival

namespace EIGS
open Set Filter Topology MeasureTheory IGS.Sec31
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

def XiNormalizedContinuousBallMeanFamilyProperties (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :=
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  letI : MeasurableSpace C(ℝ≥0, parameters.LimitSpace) := borel _
  fun globalLaws : parameters.LimitSpace → ProbabilityMeasure C(ℝ≥0, parameters.LimitSpace) =>
    ∃ constant cutoff : ℝ, 0 < constant ∧ 0 < cutoff ∧
      ∀ radius : ℝ, 0 < radius → radius ≤ cutoff → ∀ center start : parameters.LimitSpace,
        (∫⁻ path, @continuousPathBallExit parameters.LimitSpace
          (MeasuredGHP.xiCompletionDiameterMetricSpace system rulesConnected parameters.lengths
            parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
            distanceGreaterThanOne parameters.eigenpair) path center radius
          ∂(globalLaws start : Measure C(ℝ≥0, parameters.LimitSpace))) ≤
          ENNReal.ofReal (constant * radius ^
            (Real.log (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
              system.resistanceSpectralRadius rulesConnected distancePositive) /
              Real.log (system.distanceSpectralRadius rulesConnected)))

theorem xiNormalizedContinuousBallMeanFamilyProperties_of_native (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    letI : MeasurableSpace C(ℝ≥0, parameters.LimitSpace) := borel _
    ∀ globalLaws : parameters.LimitSpace → ProbabilityMeasure C(ℝ≥0, parameters.LimitSpace),
      XiNativeContinuousBallMeanFamilyProperties system rulesConnected rulesLoopless rulesUnique
        distancePositive globalLaws →
      XiNormalizedContinuousBallMeanFamilyProperties system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent distancePositive globalLaws := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  letI : MeasurableSpace C(ℝ≥0, parameters.LimitSpace) := borel _
  dsimp only
  intro globalLaws nativeProperties
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let diameter := xiCompletionDiameter system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) (zero_lt_one.trans distanceGreaterThanOne) parameters.eigenpair
  have diameterPositive : 0 < diameter := xiCompletionDiameter_positive system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  let exponent := Real.log (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
    system.resistanceSpectralRadius rulesConnected distancePositive) /
    Real.log (system.distanceSpectralRadius rulesConnected)
  dsimp only [XiNativeContinuousBallMeanFamilyProperties,
    XiNormalizedContinuousBallMeanFamilyProperties] at nativeProperties ⊢
  obtain ⟨constant, cutoff, constantPositive, cutoffPositive, nativeBounds⟩ := nativeProperties
  refine ⟨constant * diameter ^ exponent, cutoff / diameter,
    mul_pos constantPositive (Real.rpow_pos_of_pos diameterPositive exponent),
    div_pos cutoffPositive diameterPositive, ?_⟩
  intro radius radiusPositive radiusSmall center start
  have nativeSmall : diameter * radius ≤ cutoff := by
    simpa only [mul_comm] using (le_div_iff₀ diameterPositive).mp radiusSmall
  have bound := nativeBounds (diameter * radius) (mul_pos diameterPositive radiusPositive)
    nativeSmall center start
  have exitEquality (path : C(ℝ≥0, parameters.LimitSpace)) :
      @continuousPathBallExit parameters.LimitSpace
        (MeasuredGHP.xiCompletionDiameterMetricSpace system rulesConnected parameters.lengths
          parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
          distanceGreaterThanOne parameters.eigenpair) path center radius =
      @continuousPathBallExit parameters.LimitSpace parameters.instMetricSpaceLimitSpace
        path center (diameter * radius) := by
    change @continuousPathBallExit parameters.LimitSpace
      (positiveScaledMetricSpace parameters.LimitSpace diameter⁻¹ (inv_pos.mpr diameterPositive))
        path center radius = _
    rw [continuousPathBallExit_positiveScaled_eq]
    congr 1
    rw [div_inv_eq_mul, mul_comm]
  simp_rw [exitEquality]
  have powerEquality : constant * (diameter * radius) ^ exponent =
      (constant * diameter ^ exponent) * radius ^ exponent := by
    rw [Real.mul_rpow diameterPositive.le radiusPositive.le]
    ring
  rw [← powerEquality]
  exact bound

end
end EIGS

#print axioms EIGS.xiNormalizedContinuousBallMeanFamilyProperties_of_native
