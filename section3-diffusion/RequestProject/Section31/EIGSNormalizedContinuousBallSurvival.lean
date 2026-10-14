import RequestProject.Section31.EIGSContinuousPathBallSurvivalOfRules
import RequestProject.Section31.ContinuousPathScaledBallExit
import RequestProject.Section31.EIGSOriginalCountableRealisation

/-! Preserve the exact same global path family while converting genuine
native ball-exit survival to the paper's diameter-normalized completion.
The first-exit times agree after an exact change of radius. Candidate source. -/

namespace EIGS
open Set Filter Topology MeasureTheory IGS.Sec31
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

def XiNormalizedContinuousBallSurvivalFamilyProperties (system : EIGSData K)
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
    ∃ timeConstant : ℝ, 0 < timeConstant ∧ ∃ radiusThreshold : ℝ, 0 < radiusThreshold ∧
    ∀ radius : ℝ, 0 < radius → radius ≤ radiusThreshold →
    ∀ center : parameters.LimitSpace,
      (3 / 4 : ℝ) ≤ (globalLaws center : Measure C(ℝ≥0, parameters.LimitSpace)).real
        {path | ENNReal.ofReal (timeConstant * radius ^
          (Real.log (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
            system.resistanceSpectralRadius rulesConnected distancePositive) /
            Real.log (system.distanceSpectralRadius rulesConnected))) <
          @continuousPathBallExit parameters.LimitSpace
            (MeasuredGHP.xiCompletionDiameterMetricSpace system rulesConnected parameters.lengths
              parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
              distanceGreaterThanOne parameters.eigenpair) path center radius}

theorem xiNormalizedContinuousBallSurvivalFamilyProperties_of_native (system : EIGSData K)
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
      XiNativeContinuousBallSurvivalFamilyProperties system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent distancePositive globalLaws →
      XiNormalizedContinuousBallSurvivalFamilyProperties system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent distancePositive globalLaws := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  letI : MeasurableSpace C(ℝ≥0, parameters.LimitSpace) := borel _
  dsimp only
  intro globalLaws nativeProperties
  let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
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
  dsimp only [XiNativeContinuousBallSurvivalFamilyProperties,
    XiNormalizedContinuousBallSurvivalFamilyProperties] at nativeProperties ⊢
  obtain ⟨timeConstant, timeConstantPositive, radiusThreshold, radiusThresholdPositive, survives⟩ := nativeProperties
  refine ⟨timeConstant * diameter ^ exponent,
    mul_pos timeConstantPositive (Real.rpow_pos_of_pos diameterPositive exponent),
    radiusThreshold / diameter, div_pos radiusThresholdPositive diameterPositive, ?_⟩
  intro radius radiusPositive radiusSmall center
  have nativeRadiusSmall : diameter * radius ≤ radiusThreshold := by
    simpa only [mul_comm] using (le_div_iff₀ diameterPositive).mp radiusSmall
  have nativeSurvives := survives (diameter * radius) (mul_pos diameterPositive radiusPositive)
    nativeRadiusSmall center
  have timeEquality : timeConstant * (diameter * radius) ^ exponent =
      (timeConstant * diameter ^ exponent) * radius ^ exponent := by
    rw [Real.mul_rpow diameterPositive.le radiusPositive.le]
    ring
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
  rw [← timeEquality]
  exact nativeSurvives

end
end EIGS

#print axioms EIGS.xiNormalizedContinuousBallSurvivalFamilyProperties_of_native
