import RequestProject.Section31.EIGSHarmonicL2Density

/-! The actual harmonic projections of one continuous function converge
uniformly as their prescribed boundary level tends to infinity. -/

namespace EIGS

open Filter Topology
open scoped BoundedContinuousFunction

set_option maxHeartbeats 1800000

variable {K : ℕ}

section MetricEigenpair

variable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (contractionFactor : ℝ) (factorPositive : 0 < contractionFactor) (factorStrict : contractionFactor < 1)
    (stepContraction : ∀ level (oldValues : XiVtx system level → ℝ)
      (edge : XiEdge system.toRuleData (level + 1)),
      |xiHarmonicStep system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
          renormalizationEigenpair level oldValues (XiTail system (level + 1) edge) -
        xiHarmonicStep system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
          renormalizationEigenpair level oldValues (XiHead system (level + 1) edge)| ≤
        |oldValues (XiTail system level edge.1) - oldValues (XiHead system level edge.1)| * contractionFactor)

include contractionFactor factorPositive factorStrict stepContraction

theorem exists_xiContinuousHarmonic_of_step_contraction
    (initialLevel : ℕ) (initialValues : XiVtx system initialLevel → ℝ) :
    ∃ extension : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ),
      ∀ vertex : XiVertexUnion system,
        extension (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) =
          xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
            renormalizationEigenpair initialLevel initialValues vertex := by
  have initialEdgeBound : ∀ edge : XiEdge system.toRuleData initialLevel,
      |initialValues (XiTail system initialLevel edge) - initialValues (XiHead system initialLevel edge)| ≤ 2 * ‖initialValues‖ := by
    intro edge
    have firstBound := norm_le_pi_norm initialValues (XiTail system initialLevel edge)
    have secondBound := norm_le_pi_norm initialValues (XiHead system initialLevel edge)
    rw [Real.norm_eq_abs] at firstBound secondBound
    exact (abs_sub _ _).trans (by linarith)
  exact exists_xiHarmonic_completion_extension_of_edge_decay system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    initialLevel initialValues contractionFactor (2 * ‖initialValues‖) factorPositive factorStrict (by positivity)
    (xiHarmonicValues_edge_decay_of_step_contraction system rulesConnected resistanceRate ratePositive resistanceVector
      vectorPositive renormalizationEigenpair contractionFactor factorPositive.le stepContraction initialLevel initialValues
      (2 * ‖initialValues‖) initialEdgeBound)

theorem xiContinuousHarmonicProjection_uniform_tendsto
    (target : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ))
    (targetUniformContinuous : UniformContinuous target)
    (approximation : ℕ → C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ))
    (approximationAgreement : ∀ level (vertex : XiVertexUnion system),
      approximation level (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) =
        xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
          renormalizationEigenpair level
          (fun finiteVertex => target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level finiteVertex)) vertex) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    Tendsto (fun level => ‖BoundedContinuousFunction.mkOfCompact (approximation level) -
      BoundedContinuousFunction.mkOfCompact target‖) atTop (nhds 0) := by
  letI := xiUnionMetricSpace system rulesConnected lengths lengthsPositive distanceRate
    (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  apply Metric.tendsto_atTop.2
  intro tolerance tolerancePositive
  let initialBound : ℝ := tolerance * (1 - contractionFactor) / 3
  have initialBoundPositive : 0 < initialBound :=
    div_pos (mul_pos tolerancePositive (sub_pos.mpr factorStrict)) (by norm_num)
  obtain ⟨distanceTolerance, distanceTolerancePositive, targetClose⟩ := Metric.uniformContinuous_iff.1
    targetUniformContinuous (min initialBound (tolerance / 3)) (lt_min initialBoundPositive (by positivity))
  have distanceRatePositive : 0 < distanceRate := zero_lt_one.trans distanceRateGreaterThanOne
  have edgeRadiusConvergence : Tendsto (fun level : ℕ => distanceRate⁻¹ ^ level * ∑ colour, lengths colour) atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_pos.2 distanceRatePositive).le
        ((inv_lt_one₀ distanceRatePositive).mpr distanceRateGreaterThanOne)).mul_const (∑ colour, lengths colour)
  obtain ⟨threshold, radiiSmall⟩ := eventually_atTop.1
    ((edgeRadiusConvergence.eventually (gt_mem_nhds distanceTolerancePositive)).and
      ((xiFiniteNetRadius_tendsto_zero system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair).eventually (gt_mem_nhds distanceTolerancePositive)))
  refine ⟨threshold, ?_⟩
  intro level afterThreshold
  obtain ⟨edgeRadiusSmall, parentRadiusSmall⟩ := radiiSmall level afterThreshold
  let initialValues : XiVtx system level → ℝ := fun vertex =>
    target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair level vertex)
  have initialEdgeBound : ∀ edge : XiEdge system.toRuleData level,
      |initialValues (XiTail system level edge) - initialValues (XiHead system level edge)| ≤ initialBound := by
    intro edge
    have endpointsClose := (xiCompletionEmbedding_edge_distance_le system rulesConnected lengths lengthsPositive distanceRate
      distanceRatePositive metricEigenpair level edge).trans_lt edgeRadiusSmall
    have valuesClose := targetClose endpointsClose
    rw [Real.dist_eq] at valuesClose
    exact valuesClose.le.trans (min_le_left _ _)
  have edgeDecay := xiHarmonicValues_edge_decay_of_step_contraction system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive renormalizationEigenpair contractionFactor factorPositive.le stepContraction level initialValues
    initialBound initialEdgeBound
  have unionBound : ∀ vertex : XiVertexUnion system,
      |approximation level (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair vertex) -
        target (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair vertex)| ≤
        2 * tolerance / 3 := by
    intro vertex
    obtain ⟨coarseVertex, distanceBound, valueBound⟩ := xiHarmonicUnion_joint_approximation system rulesConnected lengths lengthsPositive
      distanceRate distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      level initialValues contractionFactor initialBound factorPositive factorStrict initialBoundPositive.le edgeDecay 0 vertex
    simp only [Nat.add_zero, pow_zero, mul_one] at coarseVertex distanceBound valueBound
    have completionClose : dist
        (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair vertex)
        (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair level coarseVertex) <
        distanceTolerance := by
      unfold xiCompletionEmbedding
      simp only [Function.comp_apply]
      rw [(xiCompletionUnionEmbedding_isometry system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair).dist_eq]
      exact distanceBound.trans_lt parentRadiusSmall
    have targetError := (targetClose completionClose).trans_le (min_le_right _ _)
    rw [Real.dist_eq] at targetError
    have initialAgreement := xiHarmonicUnionExtension_values system rulesConnected resistanceRate ratePositive resistanceVector
      vectorPositive renormalizationEigenpair level initialValues 0 coarseVertex
    change xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair level initialValues (xiVertexEmbedding system level coarseVertex) = initialValues coarseVertex at initialAgreement
    rw [initialAgreement] at valueBound
    have boundIdentity : initialBound / (1 - contractionFactor) = tolerance / 3 := by
      dsimp [initialBound]
      field_simp [ne_of_gt (sub_pos.mpr factorStrict)]
    rw [boundIdentity] at valueBound
    rw [approximationAgreement]
    have triangle := abs_sub_le
      (xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair level initialValues vertex)
      (initialValues coarseVertex)
      (target (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair vertex))
    have reverseTargetError : |initialValues coarseVertex -
        target (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair vertex)| <
        tolerance / 3 := by
      dsimp [initialValues]
      rw [abs_sub_comm]
      exact targetError
    linarith
  have completionBound : ∀ point, |approximation level point - target point| ≤ 2 * tolerance / 3 := by
    intro point
    exact (xiCompletionUnionEmbedding_denseRange system rulesConnected lengths lengthsPositive distanceRate distanceRatePositive metricEigenpair).induction_on
      point (isClosed_le (((approximation level).continuous.sub target.continuous).abs) continuous_const) unionBound
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  apply (BoundedContinuousFunction.norm_lt_iff_of_compact tolerancePositive).2
  intro point
  exact (completionBound point).trans_lt (by linarith)

end MetricEigenpair

end EIGS
