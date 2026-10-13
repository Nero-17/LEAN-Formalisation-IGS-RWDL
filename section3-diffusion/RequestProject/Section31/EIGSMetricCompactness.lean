import RequestProject.Section31.EIGSMetricCompletion
import RequestProject.Section2MetricCells
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-! Finite nets for the actual Xi vertex union and compactness of its metric
completion. The nets follow the actual old/private vertex maps; their radii
are derived from the finite rule graphs and the path eigenvalue. -/

namespace EIGS

private theorem geometricTailStep (ratio firstPower secondPower radius : ℝ)
    (denominatorNonzero : 1 - ratio ≠ 0) :
    secondPower * radius + radius / (1 - ratio) * (firstPower - secondPower) =
      radius / (1 - ratio) * (firstPower - secondPower * ratio) := by
  field_simp
  ring

variable {K : ℕ} (system : EIGSData K)
    (ruleConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily ruleConnected).metricLengths lengths = rate • lengths)

include ruleConnected lengthsPositive rateGreaterThanOne eigenpair

theorem xiUnionDistance_parent_bound (level : ℕ) (vertex : XiVtx system (level + 1)) :
    xiUnionDistance system lengths rate (xiVertexEmbedding system (level + 1) vertex)
        (xiVertexEmbedding system level (xiParentVertex system level vertex)) ≤
      rate⁻¹ ^ (level + 1) * xiRuleRadius system lengths := by
  rw [xiUnionDistance_symm system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair,
    ← xiVertexEmbedding_old system level (xiParentVertex system level vertex),
    xiUnionDistance_embedding system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair]
  exact xiScaledWeightedDistance_parent_bound system ruleConnected
    (fun colour => (lengthsPositive colour).le) (zero_le_one.trans rateGreaterThanOne.le) level vertex

theorem xiFiniteLevel_coarse_approximation (coarseLevel : ℕ) :
    ∀ fineLevel, coarseLevel ≤ fineLevel → ∀ vertex : XiVtx system fineLevel,
      ∃ coarseVertex : XiVtx system coarseLevel,
        xiUnionDistance system lengths rate (xiVertexEmbedding system fineLevel vertex)
            (xiVertexEmbedding system coarseLevel coarseVertex) ≤
          xiRuleRadius system lengths / (1 - rate⁻¹) *
            (rate⁻¹ ^ (coarseLevel + 1) - rate⁻¹ ^ (fineLevel + 1)) := by
  intro fineLevel levelsOrdered
  induction fineLevel, levelsOrdered using Nat.le_induction with
  | base =>
    intro vertex
    refine ⟨vertex, ?_⟩
    rw [xiUnionDistance_self system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair]
    simp
  | succ fineLevel levelsOrdered induction_hypothesis =>
    intro vertex
    obtain ⟨coarseVertex, coarseBound⟩ := induction_hypothesis (xiParentVertex system fineLevel vertex)
    refine ⟨coarseVertex, ?_⟩
    have triangle := xiUnionDistance_triangle system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair
      (xiVertexEmbedding system (fineLevel + 1) vertex)
      (xiVertexEmbedding system fineLevel (xiParentVertex system fineLevel vertex))
      (xiVertexEmbedding system coarseLevel coarseVertex)
    have parentBound := xiUnionDistance_parent_bound system ruleConnected lengths lengthsPositive
      rate rateGreaterThanOne eigenpair fineLevel vertex
    have inverseLessThanOne : rate⁻¹ < 1 := (inv_lt_one₀ (zero_lt_one.trans rateGreaterThanOne)).mpr rateGreaterThanOne
    have denominatorNonzero : 1 - rate⁻¹ ≠ 0 := ne_of_gt (sub_pos.mpr inverseLessThanOne)
    have identity : rate⁻¹ ^ (fineLevel + 1) * xiRuleRadius system lengths +
          xiRuleRadius system lengths / (1 - rate⁻¹) *
            (rate⁻¹ ^ (coarseLevel + 1) - rate⁻¹ ^ (fineLevel + 1)) =
        xiRuleRadius system lengths / (1 - rate⁻¹) *
            (rate⁻¹ ^ (coarseLevel + 1) - rate⁻¹ ^ (fineLevel + 1 + 1)) := by
      rw [pow_succ]
      exact geometricTailStep _ _ _ _ denominatorNonzero
    exact (triangle.trans (add_le_add parentBound coarseBound)).trans_eq identity

theorem xiUnion_finite_net (coarseLevel : ℕ) (vertex : XiVertexUnion system) :
    ∃ coarseVertex : XiVtx system coarseLevel,
      xiUnionDistance system lengths rate vertex (xiVertexEmbedding system coarseLevel coarseVertex) ≤
        xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (coarseLevel + 1) := by
  let fineLevel := max coarseLevel (xiUnionBirth system vertex)
  let fineVertex := xiVertexAtLevel system vertex fineLevel (le_max_right _ _)
  obtain ⟨coarseVertex, bound⟩ := xiFiniteLevel_coarse_approximation system ruleConnected lengths lengthsPositive
    rate rateGreaterThanOne eigenpair coarseLevel fineLevel (le_max_left _ _) fineVertex
  refine ⟨coarseVertex, ?_⟩
  rw [xiVertexEmbedding_atLevel] at bound
  have inverseLessThanOne : rate⁻¹ < 1 := (inv_lt_one₀ (zero_lt_one.trans rateGreaterThanOne)).mpr rateGreaterThanOne
  have coefficientNonnegative : 0 ≤ xiRuleRadius system lengths / (1 - rate⁻¹) :=
    div_nonneg (xiRuleRadius_nonnegative system (fun colour => (lengthsPositive colour).le))
      (sub_pos.mpr inverseLessThanOne).le
  exact bound.trans (mul_le_mul_of_nonneg_left
    (sub_le_self _ (pow_nonneg (inv_nonneg.mpr (zero_le_one.trans rateGreaterThanOne.le)) _)) coefficientNonnegative)

theorem xiFiniteNetRadius_tendsto_zero :
    Filter.Tendsto (fun level : ℕ =>
      xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (level + 1))
      Filter.atTop (nhds 0) := by
  have inverseLessThanOne : rate⁻¹ < 1 := (inv_lt_one₀ (zero_lt_one.trans rateGreaterThanOne)).mpr rateGreaterThanOne
  have convergence := tendsto_pow_atTop_nhds_zero_of_lt_one
    (inv_nonneg.mpr (zero_le_one.trans rateGreaterThanOne.le)) inverseLessThanOne
  simpa only [mul_zero] using
    (convergence.comp (Filter.tendsto_add_atTop_nat 1)).const_mul (xiRuleRadius system lengths / (1 - rate⁻¹))

theorem xiUnion_totallyBounded :
    letI := xiUnionMetricSpace system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair
    TotallyBounded (Set.univ : Set (XiVertexUnion system)) := by
  letI := xiUnionMetricSpace system ruleConnected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) eigenpair
  apply Metric.totallyBounded_iff.mpr
  intro tolerance tolerancePositive
  have eventuallySmall := (xiFiniteNetRadius_tendsto_zero system ruleConnected lengths lengthsPositive
    rate rateGreaterThanOne eigenpair).eventually (gt_mem_nhds tolerancePositive)
  obtain ⟨level, levelBound⟩ := eventuallySmall.exists
  refine ⟨Set.range (xiVertexEmbedding system level), Set.finite_range _, ?_⟩
  intro vertex _
  obtain ⟨finiteVertex, approximation⟩ := xiUnion_finite_net system ruleConnected lengths lengthsPositive
    rate rateGreaterThanOne eigenpair level vertex
  simp only [Set.mem_iUnion]
  exact ⟨xiVertexEmbedding system level finiteVertex, ⟨finiteVertex, rfl⟩,
    approximation.trans_lt levelBound⟩

theorem xiCompletion_compactSpace :
    CompactSpace (XiMetricCompletion system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) := by
  letI := xiUnionMetricSpace system ruleConnected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) eigenpair
  have imageBounded := (xiUnion_totallyBounded system ruleConnected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair).image
      (xiCompletionUnionEmbedding_isometry system ruleConnected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair).uniformContinuous
  rw [Set.image_univ] at imageBounded
  have closureBounded := imageBounded.closure
  rw [(xiCompletionUnionEmbedding_denseRange system ruleConnected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) eigenpair).closure_range] at closureBounded
  exact isCompact_univ_iff.mp (isCompact_iff_totallyBounded_isComplete.mpr
    ⟨closureBounded, isClosed_univ.isComplete⟩)

end EIGS

#print axioms EIGS.xiFiniteLevel_coarse_approximation
#print axioms EIGS.xiUnion_finite_net
#print axioms EIGS.xiUnion_totallyBounded
#print axioms EIGS.xiCompletion_compactSpace
