import RequestProject.Section31.EIGSContinuousBallGeometricMeanOfRules
import RequestProject.Section31.GeometricExitMeanOptimization

/-! The all-radius native continuous expected-exit bound, uniform in both
the ball center and the starting point, for the same given global family. -/

namespace EIGS
open Set Filter Topology MeasureTheory IGS.Sec31
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 7000000
variable {K : ℕ}

def XiNativeContinuousBallMeanFamilyProperties (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :=
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  letI : MeasurableSpace C(ℝ≥0, parameters.LimitSpace) := borel _
  fun globalLaws : parameters.LimitSpace → ProbabilityMeasure C(ℝ≥0, parameters.LimitSpace) =>
    ∃ constant cutoff : ℝ, 0 < constant ∧ 0 < cutoff ∧
      ∀ radius : ℝ, 0 < radius → radius ≤ cutoff → ∀ center start : parameters.LimitSpace,
        (∫⁻ path, @continuousPathBallExit parameters.LimitSpace parameters.instMetricSpaceLimitSpace
          path center radius ∂(globalLaws start : Measure C(ℝ≥0, parameters.LimitSpace))) ≤
          ENNReal.ofReal (constant * radius ^
            (Real.log (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
              system.resistanceSpectralRadius rulesConnected distancePositive) /
              Real.log (system.distanceSpectralRadius rulesConnected)))

theorem xiNativeContinuousBallMeanFamilyProperties_of_restriction (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalization : ℝ) (normalizationPositive : 0 < normalization) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    letI : MeasurableSpace C(ℝ≥0, parameters.LimitSpace) := borel _
    ∀ globalLaws : parameters.LimitSpace → ProbabilityMeasure C(ℝ≥0, parameters.LimitSpace),
      XiNativeGlobalContinuousRestrictionFamilyProperties system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent distancePositive normalization normalizationPositive globalLaws →
      XiNativeContinuousBallMeanFamilyProperties system rulesConnected rulesLoopless rulesUnique
        distancePositive globalLaws := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  letI : MeasurableSpace C(ℝ≥0, parameters.LimitSpace) := borel _
  dsimp only
  intro globalLaws properties
  dsimp only [XiNativeContinuousBallMeanFamilyProperties]
  obtain ⟨upper, radiusScale, upperPositive, radiusScalePositive, geometricBounds⟩ :=
    xiNativeContinuousBall_geometric_mean_upper_of_restriction system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent distancePositive normalization normalizationPositive globalLaws properties
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  have timeGreaterThanOne : 1 < realMatrixSpectralRadius (massMatrixR system.toRuleData) *
      system.resistanceSpectralRadius rulesConnected distancePositive := by
    have squareBound := system.distanceSpectralRadius_sq_le_mass_mul_resistance
      rulesConnected rulesLoopless rulesUnique distancePositive
    have distanceBound := system.two_le_distanceSpectralRadius rulesConnected rulesUnique
      plantingNonadjacent distancePositive
    nlinarith
  obtain ⟨constant, cutoff, constantPositive, cutoffPositive, choice⟩ := geometric_exit_mean_radius_choice
    (system.distanceSpectralRadius rulesConnected)
    (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
      system.resistanceSpectralRadius rulesConnected distancePositive) radiusScale upper
    distanceGreaterThanOne timeGreaterThanOne radiusScalePositive upperPositive
  refine ⟨constant, cutoff, constantPositive, cutoffPositive, ?_⟩
  intro radius radiusPositive radiusSmall center start
  obtain ⟨level, levelPositive, radiusBound, timeBound⟩ := choice radius radiusPositive radiusSmall
  exact (lintegral_mono fun path => continuousPathBallExit_mono_radius path center radiusBound).trans
    ((geometricBounds level levelPositive center start).trans (ENNReal.ofReal_le_ofReal timeBound))

end
end EIGS

#print axioms EIGS.xiNativeContinuousBallMeanFamilyProperties_of_restriction
