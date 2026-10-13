import RequestProject.Section31.EIGSHarmonicContinuity
import RequestProject.Section31.EIGSLimitCompact
import Mathlib.Topology.UniformSpace.HeineCantor

set_option maxHeartbeats 1800000

/-! Actual continuous harmonic splines are uniformly dense on the constructed
compact completion. Small metric edge lengths control the prescribed boundary
oscillation; the proved joint parent estimate controls every interior value. -/

namespace EIGS

open Filter Topology

variable {K : ℕ}

theorem xiCompletionEmbedding_edge_distance_le (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (ratePositive : 0 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (level : ℕ) (edge : XiEdge system.toRuleData level) :
    dist (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate ratePositive metricEigenpair level
        (XiTail system level edge))
      (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate ratePositive metricEigenpair level
        (XiHead system level edge)) ≤ distanceRate⁻¹ ^ level * ∑ colour, lengths colour := by
  letI := xiUnionMetricSpace system rulesConnected lengths lengthsPositive distanceRate ratePositive metricEigenpair
  unfold xiCompletionEmbedding
  simp only [Function.comp_apply]
  rw [(xiCompletionUnionEmbedding_isometry system rulesConnected lengths lengthsPositive distanceRate ratePositive metricEigenpair).dist_eq]
  change xiUnionDistance system lengths distanceRate (xiVertexEmbedding system level (XiTail system level edge))
    (xiVertexEmbedding system level (XiHead system level edge)) ≤ _
  rw [xiUnionDistance_embedding system rulesConnected lengths lengthsPositive distanceRate ratePositive metricEigenpair]
  exact mul_le_mul_of_nonneg_left
    (((XiNetwork system level).weightedDistance_edge (fun colour => (lengthsPositive colour).le) edge).trans
      (Finset.single_le_sum (fun colour _ => (lengthsPositive colour).le) (Finset.mem_univ _)))
    (pow_nonneg (inv_pos.2 ratePositive).le _)

theorem exists_xiHarmonic_uniform_approximation_of_step_contraction
    (system : EIGSData K) (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (resistanceRate : ℝ) (resistanceRatePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (contractionFactor : ℝ) (factorPositive : 0 < contractionFactor) (factorStrict : contractionFactor < 1)
    (stepContraction : ∀ level (oldValues : XiVtx system level → ℝ) (edge : XiEdge system.toRuleData (level + 1)),
      |xiHarmonicStep system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
          renormalizationEigenpair level oldValues (XiTail system (level + 1) edge) -
        xiHarmonicStep system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
          renormalizationEigenpair level oldValues (XiHead system (level + 1) edge)| ≤
        |oldValues (XiTail system level edge.1) - oldValues (XiHead system level edge.1)| * contractionFactor)
    (target : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ))
    (targetUniformContinuous : UniformContinuous target) (tolerance : ℝ) (tolerancePositive : 0 < tolerance) :
    ∃ initialLevel : ℕ, ∃ initialValues : XiVtx system initialLevel → ℝ,
      ∃ extension : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ),
        (∀ offset (vertex : XiVtx system (initialLevel + offset)),
          extension (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair (initialLevel + offset) vertex) =
          xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
            renormalizationEigenpair initialLevel initialValues offset vertex) ∧
        ∀ point, |extension point - target point| < tolerance := by
  letI := xiUnionMetricSpace system rulesConnected lengths lengthsPositive distanceRate
    (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair
  let initialBound : ℝ := tolerance * (1 - contractionFactor) / 3
  have initialBoundPositive : 0 < initialBound :=
    div_pos (mul_pos tolerancePositive (sub_pos.mpr factorStrict)) (by norm_num)
  obtain ⟨distanceTolerance, distanceTolerancePositive, targetClose⟩ := Metric.uniformContinuous_iff.1
    targetUniformContinuous (min initialBound (tolerance / 3)) (lt_min initialBoundPositive (by positivity))
  have ratePositive : 0 < distanceRate := zero_lt_one.trans distanceRateGreaterThanOne
  have inverseStrict : distanceRate⁻¹ < 1 := (inv_lt_one₀ ratePositive).mpr distanceRateGreaterThanOne
  have edgeRadiusConvergence : Tendsto (fun level : ℕ => distanceRate⁻¹ ^ level * ∑ colour, lengths colour) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_pos.2 ratePositive).le inverseStrict).mul_const (∑ colour, lengths colour)
  have edgeSmall := edgeRadiusConvergence.eventually (gt_mem_nhds distanceTolerancePositive)
  have parentSmall := (xiFiniteNetRadius_tendsto_zero system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair).eventually (gt_mem_nhds distanceTolerancePositive)
  obtain ⟨initialLevel, edgeRadiusSmall, parentRadiusSmall⟩ := (edgeSmall.and parentSmall).exists
  let initialValues : XiVtx system initialLevel → ℝ := fun vertex =>
    target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate ratePositive metricEigenpair initialLevel vertex)
  have initialEdgeBound : ∀ edge : XiEdge system.toRuleData initialLevel,
      |initialValues (XiTail system initialLevel edge) - initialValues (XiHead system initialLevel edge)| ≤ initialBound := by
    intro edge
    have endpointsClose := (xiCompletionEmbedding_edge_distance_le system rulesConnected lengths lengthsPositive distanceRate
      ratePositive metricEigenpair initialLevel edge).trans_lt edgeRadiusSmall
    have valuesClose := targetClose endpointsClose
    rw [Real.dist_eq] at valuesClose
    exact valuesClose.le.trans (min_le_left _ _)
  have edgeDecay := xiHarmonicValues_edge_decay_of_step_contraction system rulesConnected resistanceRate resistanceRatePositive
    resistanceVector resistanceVectorPositive renormalizationEigenpair contractionFactor factorPositive.le stepContraction
    initialLevel initialValues initialBound initialEdgeBound
  obtain ⟨extension, extensionValues⟩ := exists_xiHarmonic_completion_extension_of_edge_decay
    system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
    resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair
    initialLevel initialValues contractionFactor initialBound factorPositive factorStrict initialBoundPositive.le edgeDecay
  refine ⟨initialLevel, initialValues, extension, ?_, ?_⟩
  · intro offset vertex
    exact (extensionValues (xiVertexEmbedding system (initialLevel + offset) vertex)).trans
      (xiHarmonicUnionExtension_values system rulesConnected resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset vertex)
  · have unionBound : ∀ vertex : XiVertexUnion system,
        |extension (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate ratePositive metricEigenpair vertex) -
          target (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate ratePositive metricEigenpair vertex)| ≤
        2 * tolerance / 3 := by
      intro vertex
      obtain ⟨coarseVertex, distanceBound, valueBound⟩ := xiHarmonicUnion_joint_approximation
        system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
        resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair
        initialLevel initialValues contractionFactor initialBound factorPositive factorStrict initialBoundPositive.le edgeDecay 0 vertex
      simp only [Nat.add_zero, pow_zero, mul_one] at coarseVertex distanceBound valueBound
      have completionClose : dist
          (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate ratePositive metricEigenpair vertex)
          (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate ratePositive metricEigenpair initialLevel coarseVertex) <
          distanceTolerance := by
        unfold xiCompletionEmbedding
        simp only [Function.comp_apply]
        rw [(xiCompletionUnionEmbedding_isometry system rulesConnected lengths lengthsPositive distanceRate ratePositive metricEigenpair).dist_eq]
        exact distanceBound.trans_lt parentRadiusSmall
      have targetError := (targetClose completionClose).trans_le (min_le_right _ _)
      rw [Real.dist_eq] at targetError
      have initialAgreement := xiHarmonicUnionExtension_values system rulesConnected resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive renormalizationEigenpair initialLevel initialValues 0 coarseVertex
      change xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
        renormalizationEigenpair initialLevel initialValues (xiVertexEmbedding system initialLevel coarseVertex) = initialValues coarseVertex
        at initialAgreement
      rw [initialAgreement] at valueBound
      have boundIdentity : initialBound / (1 - contractionFactor) = tolerance / 3 := by
        dsimp [initialBound]
        field_simp [ne_of_gt (sub_pos.mpr factorStrict)]
      rw [boundIdentity] at valueBound
      rw [extensionValues]
      have triangle := abs_sub_le
        (xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
          renormalizationEigenpair initialLevel initialValues vertex) (initialValues coarseVertex)
        (target (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate ratePositive metricEigenpair vertex))
      have reverseTargetError : |initialValues coarseVertex -
          target (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate ratePositive metricEigenpair vertex)| <
          tolerance / 3 := by
        dsimp [initialValues]
        rw [abs_sub_comm]
        exact targetError
      linarith
    intro point
    have completionBound : |extension point - target point| ≤ 2 * tolerance / 3 :=
      (xiCompletionUnionEmbedding_denseRange system rulesConnected lengths lengthsPositive distanceRate ratePositive metricEigenpair).induction_on
        point (isClosed_le ((extension.continuous.sub target.continuous).abs) continuous_const) unionBound
    exact completionBound.trans_lt (by linarith)

theorem exists_xiContinuousHarmonic_dense_core_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    ∃ resistanceRate : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ resistanceRatePositive : 0 < resistanceRate,
      ∃ resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∀ (target : C(parameters.LimitSpace, ℝ)) (tolerance : ℝ), 0 < tolerance →
        ∃ initialLevel : ℕ, ∃ initialValues : XiVtx system initialLevel → ℝ,
          ∃ extension : C(parameters.LimitSpace, ℝ),
            (∀ offset (vertex : XiVtx system (initialLevel + offset)),
              extension (parameters.vertexEmbedding (initialLevel + offset) vertex) =
              xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
                renormalizationEigenpair initialLevel initialValues offset vertex) ∧
            ∀ point, |extension point - target point| < tolerance := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  letI : CompactSpace parameters.LimitSpace := parameters.limit_compactSpace rulesUnique plantingNonadjacent distancePositive
  have distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  have oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro oneColour colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj (system.plant_ne colour) (plantingNonadjacent colour)
  obtain ⟨resistanceRate, resistanceVector, resistanceRatePositive, resistanceVectorPositive, renormalizationEigenpair,
      contractionFactor, factorPositive, factorStrict, stepContraction⟩ :=
    exists_xiHarmonic_strict_contraction system rulesConnected distancePositive oneColourDistance
  refine ⟨resistanceRate, resistanceVector, resistanceRatePositive, resistanceVectorPositive, renormalizationEigenpair, ?_⟩
  intro target tolerance tolerancePositive
  have targetUniformContinuous : UniformContinuous target :=
    CompactSpace.uniformContinuous_of_continuous target.continuous
  exact exists_xiHarmonic_uniform_approximation_of_step_contraction system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair resistanceRate resistanceRatePositive
    resistanceVector resistanceVectorPositive renormalizationEigenpair contractionFactor factorPositive factorStrict stepContraction
    target targetUniformContinuous tolerance tolerancePositive

end EIGS
