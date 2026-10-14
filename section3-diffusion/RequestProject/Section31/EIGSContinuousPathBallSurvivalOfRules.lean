import RequestProject.Section31.EIGSNativeFinitePrefixSurvival
import RequestProject.Section31.EIGSMovingStartGlobalRestrictionOfRules
import RequestProject.Section31.GeometricBallSurvivalTimeChoice

/-! Genuine exit survival for every actual native global path family with
the proved moving-start restriction interface. Finite maximal displacement,
uniform weak convergence, a closed countable-prefix event and continuity fill
the survival conclusion. No target exit estimate or coupling is assumed.
Candidate source, awaiting independent compilation. -/

namespace EIGS
open Set Filter Topology MeasureTheory ProbabilityTheory IGS.Sec31
open IGS.Sec31.DiscreteMarkov
open scoped Classical NNReal ENNReal UniformConvergence
noncomputable section
set_option maxHeartbeats 7000000
variable {K : ℕ}

def XiNativeGlobalRestrictionFamilyProperties (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalization : ℝ) (normalizationPositive : 0 < normalization) :=
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  letI : MeasurableSpace parameters.LimitSpace := borel _
  letI : BorelSpace parameters.LimitSpace := ⟨rfl⟩
  letI : MeasurableSpace C(ℝ≥0, parameters.LimitSpace) := borel _
  let rates := xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive
    normalization normalizationPositive
  let paths := fun horizon => finiteHorizonStepPaths horizon rates parameters.vertexEmbedding
  fun globalLaws : parameters.LimitSpace → ProbabilityMeasure C(ℝ≥0, parameters.LimitSpace) =>
    ∀ center : parameters.LimitSpace,
      ∃ laws : (horizon : ℝ≥0) → ProbabilityMeasure (FiniteSupportPathSpace (paths horizon)),
      (∀ starts : ∀ level, XiVtx system level,
        Tendsto (fun level => parameters.vertexEmbedding level (starts level)) atTop (𝓝 center) →
        ∀ horizon, Tendsto (fun level => finiteHorizonStepLaw horizon rates parameters.vertexEmbedding
          (fun level => xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
          (fun level => (⟨Measure.dirac (starts level), inferInstance⟩ : ProbabilityMeasure (XiVtx system level))) level)
          atTop (𝓝 (laws horizon))) ∧
      (∀ horizon,
        (laws horizon : Measure (FiniteSupportPathSpace (paths horizon))).map
          (fun path => UniformFun.toFun path.val) =
          (globalLaws center : Measure C(ℝ≥0, parameters.LimitSpace)).map
            (fun path => fun time : Icc (0 : ℝ) (horizon : ℝ) => path ⟨time.val, time.property.1⟩))

def XiNativeContinuousBallSurvivalFamilyProperties (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :=
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
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
          @continuousPathBallExit parameters.LimitSpace parameters.instMetricSpaceLimitSpace path center radius}

theorem xiNativeContinuousBallSurvivalFamilyProperties_of_restriction (system : EIGSData K)
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
      XiNativeGlobalRestrictionFamilyProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive normalization normalizationPositive globalLaws →
      XiNativeContinuousBallSurvivalFamilyProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive globalLaws := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  letI : MeasurableSpace parameters.LimitSpace := borel _
  letI : BorelSpace parameters.LimitSpace := ⟨rfl⟩
  letI : MeasurableSpace C(ℝ≥0, parameters.LimitSpace) := borel _
  letI : BorelSpace C(ℝ≥0, parameters.LimitSpace) := ⟨rfl⟩
  dsimp only
  intro globalLaws restrictionFamily
  dsimp only [XiNativeGlobalRestrictionFamilyProperties] at restrictionFamily
  dsimp only [XiNativeContinuousBallSurvivalFamilyProperties]
  let rates := xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive
    normalization normalizationPositive
  obtain ⟨fraction, fractionPositive, count, finitePrefix⟩ :=
    exists_xiNativeFinitePrefixSurvival_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive normalization normalizationPositive
  let timeRate := realMatrixSpectralRadius (massMatrixR system.toRuleData) *
    system.resistanceSpectralRadius rulesConnected distancePositive
  have timeGreaterThanOne : 1 < timeRate := by
    have squareBound := system.distanceSpectralRadius_sq_le_mass_mul_resistance
      rulesConnected rulesLoopless rulesUnique distancePositive
    have distanceBound := system.two_le_distanceSpectralRadius rulesConnected rulesUnique
      plantingNonadjacent distancePositive
    dsimp only [timeRate]
    nlinarith
  let radiusScale : ℝ := 3 * ((count + 2 : ℝ) * (3 * xiRuleRadius system parameters.lengths + 1))
  have radiusScalePositive : 0 < radiusScale := by
    have radiusNonnegative := xiRuleRadius_nonnegative system (fun colour => (parameters.lengthsPositive colour).le)
    dsimp only [radiusScale]
    positivity
  obtain ⟨timeConstant, timeConstantPositive, chooseLevel⟩ := geometric_ball_survival_time_choice
    (system.distanceSpectralRadius rulesConnected) timeRate radiusScale fraction
    distanceGreaterThanOne timeGreaterThanOne radiusScalePositive fractionPositive
  refine ⟨timeConstant, timeConstantPositive, radiusScale, radiusScalePositive, ?_⟩
  intro radius radiusPositive radiusSmall center
  obtain ⟨coarse, spatialBound, timeBound⟩ := chooseLevel radius radiusPositive radiusSmall
  let horizon : ℝ≥0 := ⟨timeConstant * radius ^ (Real.log timeRate / Real.log
    (system.distanceSpectralRadius rulesConnected)), by positivity⟩
  let spatialRadius := (count + 2 : ℝ) * ((3 * xiRuleRadius system parameters.lengths + 1) *
    (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse)
  have spatialPositive : 0 < spatialRadius := by
    have radiusNonnegative := xiRuleRadius_nonnegative system (fun colour => (parameters.lengthsPositive colour).le)
    dsimp only [spatialRadius]
    positivity
  have innerMargin : 2 * spatialRadius < radius := by
    have threeBound : 3 * spatialRadius ≤ radius := by
      simpa only [spatialRadius, radiusScale, mul_assoc] using spatialBound
    linarith
  obtain ⟨starts, startsConverge⟩ := parameters.exists_moving_starts center
  obtain ⟨laws, movingConvergence, globalRestriction⟩ := restrictionFamily center
  have shifted : Tendsto (fun steps : ℕ => coarse + steps) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat coarse
  letI : Nonempty (Icc (0 : ℝ) (horizon : ℝ)) := ⟨⟨0, le_rfl, horizon.property⟩⟩
  let times := TopologicalSpace.denseSeq (Icc (0 : ℝ) (horizon : ℝ))
  have finiteBad := finitePrefix coarse horizon timeBound times center starts startsConverge
  have survives := finiteSupport_weak_global_ball_survival horizon
    (finiteHorizonStepPaths horizon rates parameters.vertexEmbedding) times
    (TopologicalSpace.denseRange_denseSeq _) center (2 * spatialRadius) radius innerMargin
    (fun steps => finiteHorizonStepLaw horizon rates parameters.vertexEmbedding
      (fun level => xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
      (fun level => (⟨Measure.dirac (starts level), inferInstance⟩ : ProbabilityMeasure (XiVtx system level)))
      (coarse + steps)) (laws horizon)
    ((movingConvergence starts startsConverge horizon).comp shifted)
    (globalLaws center) (globalRestriction horizon) finiteBad
  simpa only [horizon, ENNReal.ofReal_coe_nnreal] using survives

end
end EIGS

#print axioms EIGS.xiNativeContinuousBallSurvivalFamilyProperties_of_restriction
