import RequestProject.Section31.EIGSFiniteCompletionBallNativeMean
import RequestProject.Section31.EIGSFiniteCompletionBallProper
import RequestProject.Section31.FiniteSupportWeakExitMeanUpper
import RequestProject.Section31.EIGSContinuousPathBallSurvivalOfRules
import RequestProject.Section31.EIGSHarmonicLipschitzApproximation

/-! Original finite rules supply an arbitrary-source continuous ball mean
on every positive coarse scale. All finite-horizon laws and the global
path family are the same given native family; no continuous exit estimate
or coupling is an input. The subsequent all-radius optimization remains
a separate consumer. -/

namespace EIGS
open Set Filter Topology MeasureTheory ProbabilityTheory IGS.Sec31
open IGS.Sec31.DiscreteMarkov
open scoped Classical NNReal ENNReal UniformConvergence
noncomputable section
set_option maxHeartbeats 10000000
variable {K : ℕ}

def XiNativeGlobalContinuousRestrictionFamilyProperties (system : EIGSData K)
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
  let rates := xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive normalization normalizationPositive
  let paths := fun horizon => finiteHorizonStepPaths horizon rates parameters.vertexEmbedding
  fun globalLaws : parameters.LimitSpace → ProbabilityMeasure C(ℝ≥0, parameters.LimitSpace) =>
    ∀ start : parameters.LimitSpace,
      ∃ laws : (horizon : ℝ≥0) → ProbabilityMeasure (FiniteSupportPathSpace (paths horizon)),
        (∀ starts : ∀ level, XiVtx system level,
          Tendsto (fun level => parameters.vertexEmbedding level (starts level)) atTop (𝓝 start) →
          ∀ horizon, Tendsto (fun level => finiteHorizonStepLaw horizon rates parameters.vertexEmbedding
            (fun level => xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
            (fun level => (⟨Measure.dirac (starts level), inferInstance⟩ : ProbabilityMeasure (XiVtx system level))) level)
            atTop (𝓝 (laws horizon))) ∧
        (∀ horizon, ∀ᵐ path ∂(laws horizon : Measure (FiniteSupportPathSpace (paths horizon))),
          Continuous (UniformFun.toFun path.val)) ∧
        (∀ horizon, (laws horizon : Measure (FiniteSupportPathSpace (paths horizon))).map
            (fun path => UniformFun.toFun path.val) =
          (globalLaws start : Measure C(ℝ≥0, parameters.LimitSpace)).map
            (fun path => fun time : Icc (0 : ℝ) (horizon : ℝ) => path ⟨time.val, time.property.1⟩))

theorem xiNativeContinuousBall_geometric_mean_upper_of_restriction (system : EIGSData K)
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
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair
    letI : MeasurableSpace parameters.LimitSpace := borel _
    letI : BorelSpace parameters.LimitSpace := ⟨rfl⟩
    letI : MeasurableSpace C(ℝ≥0, parameters.LimitSpace) := borel _
    ∀ globalLaws : parameters.LimitSpace → ProbabilityMeasure C(ℝ≥0, parameters.LimitSpace),
      XiNativeGlobalContinuousRestrictionFamilyProperties system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent distancePositive normalization normalizationPositive globalLaws →
      ∃ upper radiusScale : ℝ, 0 < upper ∧ 0 < radiusScale ∧
        ∀ coarse, 1 ≤ coarse → ∀ center start : parameters.LimitSpace,
          (∫⁻ path, @continuousPathBallExit parameters.LimitSpace parameters.instMetricSpaceLimitSpace
            path center (radiusScale * (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse)
            ∂(globalLaws start : Measure C(ℝ≥0, parameters.LimitSpace))) ≤
            ENNReal.ofReal (upper * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
              system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse) := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  letI : MeasurableSpace parameters.LimitSpace := borel _
  letI : BorelSpace parameters.LimitSpace := ⟨rfl⟩
  letI : MeasurableSpace C(ℝ≥0, parameters.LimitSpace) := borel _
  letI : BorelSpace C(ℝ≥0, parameters.LimitSpace) := ⟨rfl⟩
  let rates := xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive normalization normalizationPositive
  dsimp only
  intro globalLaws properties
  obtain ⟨lowerLength, lowerLengthPositive, lengthLower⟩ :=
    exists_positive_colour_length_lower_bound system parameters.lengths parameters.lengthsPositive
  obtain ⟨upper, upperPositive, finiteMeanBounds⟩ := xiFiniteCompletionBall_native_mean_upper
    system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
    normalization normalizationPositive parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
    lowerLength lowerLengthPositive lengthLower
  refine ⟨upper, lowerLength / 2, upperPositive, by positivity, ?_⟩
  intro coarse coarsePositive center start
  let outerRadius := lowerLength * (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse
  have outerPositive : 0 < outerRadius :=
    mul_pos lowerLengthPositive (pow_pos (inv_pos.mpr (zero_lt_one.trans distanceGreaterThanOne)) coarse)
  obtain ⟨centers, centersConverge⟩ := parameters.exists_moving_starts center
  obtain ⟨starts, startsConverge⟩ := parameters.exists_moving_starts start
  obtain ⟨laws, convergence, limitContinuous, restriction⟩ := properties start
  have shifted : Tendsto (fun steps : ℕ => coarse + steps) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat coarse
  have centerNear : ∀ᶠ steps in atTop,
      dist (parameters.vertexEmbedding (coarse + steps) (centers (coarse + steps))) center ≤
        outerRadius - outerRadius / 2 := by
    have centerDistance : Tendsto (fun steps : ℕ =>
        dist (parameters.vertexEmbedding (coarse + steps) (centers (coarse + steps))) center)
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [Function.comp_apply, dist_self] using
        (centersConverge.comp shifted).dist (tendsto_const_nhds : Tendsto (fun _ : ℕ => center) atTop (𝓝 center))
    have marginPositive : 0 < outerRadius - outerRadius / 2 := by linarith
    exact (centerDistance.eventually (gt_mem_nhds marginPositive)).mono (fun _ near => near.le)
  have bound := finiteSupport_weak_global_exit_mean_upper rates
    (xiNativeFiniteJumpRateNNReal_positive system rulesConnected distancePositive normalization normalizationPositive)
    parameters.vertexEmbedding
    (fun level => xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
    (fun level => (⟨Measure.dirac (starts level), inferInstance⟩ : ProbabilityMeasure (XiVtx system level)))
    (fun steps => coarse + steps) laws
    (fun horizon => (convergence starts startsConverge horizon).comp shifted)
    limitContinuous (globalLaws start) restriction center centers (outerRadius / 2) outerRadius centerNear
    (ENNReal.ofReal (upper * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
      system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse)) (by
      intro steps
      have proper := xiFiniteCompletionBall_complement_nonempty system rulesConnected plantingNonadjacent
        parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
        distanceGreaterThanOne parameters.eigenpair lowerLength lowerLengthPositive lengthLower
        coarse coarsePositive steps (centers (coarse + steps))
      have finiteBound := finiteMeanBounds coarse coarsePositive steps
        (centers (coarse + steps)) (starts (coarse + steps))
      have rateRealPositive : 0 < (rates (coarse + steps) : ℝ) :=
        xiNativeFiniteJumpRateNNReal_positive system rulesConnected distancePositive
          normalization normalizationPositive (coarse + steps)
      rw [xiNativeDiscreteKernel, graphFloorExitTime_lintegral _ _
        (xiSimpleGraph_connected system rulesConnected (coarse + steps)) proper]
      rw [← ENNReal.ofReal_coe_nnreal (p := rates (coarse + steps)),
        ← ENNReal.ofReal_div_of_pos rateRealPositive]
      exact ENNReal.ofReal_le_ofReal finiteBound)
  simpa only [outerRadius, div_mul_eq_mul_div] using bound

end
end EIGS

#print axioms EIGS.xiNativeContinuousBall_geometric_mean_upper_of_restriction
