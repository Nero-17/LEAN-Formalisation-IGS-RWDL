import RequestProject.Section31.EIGSMetricCompactness
import Mathlib.Topology.MetricSpace.GromovHausdorff

/-! Quantitative Hausdorff and Gromov--Hausdorff approximation of the actual
compact completion by its finite weighted Xi graphs. -/

namespace EIGS

open Filter Topology Metric Set GromovHausdorff

variable {K : ℕ} (system : EIGSData K)
    (ruleConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily ruleConnected).metricLengths lengths = rate • lengths)

include ruleConnected lengthsPositive rateGreaterThanOne eigenpair

theorem xiCompletion_finite_net (level : ℕ)
    (point : XiMetricCompletion system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) :
    ∃ vertex : XiVtx system level,
      dist point (xiCompletionEmbedding system ruleConnected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair level vertex) ≤
        xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (level + 1) := by
  classical
  letI := xiUnionMetricSpace system ruleConnected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) eigenpair
  let radius := xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (level + 1)
  let cover : Set (XiMetricCompletion system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) :=
    {point | ∃ vertex : XiVtx system level,
      dist point (xiCompletionEmbedding system ruleConnected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair level vertex) ≤ radius}
  have coverClosed : IsClosed cover := by
    have coverIdentity : cover = ⋃ vertex : XiVtx system level,
        closedBall (xiCompletionEmbedding system ruleConnected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair level vertex) radius := by
      ext point
      simp only [cover, mem_setOf_eq, mem_iUnion, mem_closedBall]
    rw [coverIdentity]
    exact isClosed_iUnion_of_finite (fun _ => isClosed_closedBall)
  have coverDense : range (xiCompletionUnionEmbedding system ruleConnected lengths lengthsPositive
      rate (zero_lt_one.trans rateGreaterThanOne) eigenpair) ⊆ cover := by
    rintro _ ⟨vertex, rfl⟩
    obtain ⟨coarseVertex, bound⟩ := xiUnion_finite_net system ruleConnected lengths lengthsPositive
      rate rateGreaterThanOne eigenpair level vertex
    refine ⟨coarseVertex, ?_⟩
    change dist (xiCompletionUnionEmbedding system ruleConnected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair vertex)
      (xiCompletionUnionEmbedding system ruleConnected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair (xiVertexEmbedding system level coarseVertex)) ≤ radius
    rw [(xiCompletionUnionEmbedding_isometry system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair).dist_eq]
    exact bound
  have closureCovered := coverClosed.closure_subset_iff.mpr coverDense
  rw [(xiCompletionUnionEmbedding_denseRange system ruleConnected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) eigenpair).closure_range] at closureCovered
  exact closureCovered (mem_univ point)

theorem xiFiniteLevel_hausdorffDist_le (level : ℕ) :
    hausdorffDist
      (range (xiCompletionEmbedding system ruleConnected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair level)) univ ≤
      xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (level + 1) := by
  have radiusNonnegative : 0 ≤
      xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (level + 1) := by
    exact mul_nonneg
      (div_nonneg (xiRuleRadius_nonnegative system (fun colour => (lengthsPositive colour).le))
        (sub_pos.mpr ((inv_lt_one₀ (zero_lt_one.trans rateGreaterThanOne)).mpr rateGreaterThanOne)).le)
      (pow_nonneg (inv_nonneg.mpr (zero_le_one.trans rateGreaterThanOne.le)) _)
  apply hausdorffDist_le_of_mem_dist radiusNonnegative
  · intro point _
    exact ⟨point, mem_univ _, (dist_self _).le.trans radiusNonnegative⟩
  · intro point _
    obtain ⟨vertex, bound⟩ := xiCompletion_finite_net system ruleConnected lengths lengthsPositive
      rate rateGreaterThanOne eigenpair level point
    exact ⟨_, mem_range_self vertex, by simpa only [dist_comm] using bound⟩

theorem xiFiniteLevel_hausdorffDist_tendsto_zero :
    Tendsto (fun level => hausdorffDist
      (range (xiCompletionEmbedding system ruleConnected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair level)) univ) atTop (nhds 0) := by
  exact squeeze_zero (fun _ => hausdorffDist_nonneg)
    (xiFiniteLevel_hausdorffDist_le system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair)
    (xiFiniteNetRadius_tendsto_zero system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair)

theorem xiFiniteLevel_ghDist_le (level : ℕ) :
    letI := xiLevelMetricSpace system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) level
    letI := xiCompletion_compactSpace system ruleConnected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair
    letI : Nonempty (XiVtx system level) := ⟨by simpa only [Nat.zero_add] using xiLiftVertices system 0 level true⟩
    letI : Nonempty (XiMetricCompletion system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) :=
      ⟨xiCompletionEmbedding system ruleConnected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair level (by simpa only [Nat.zero_add] using xiLiftVertices system 0 level true)⟩
    ghDist (XiVtx system level)
      (XiMetricCompletion system ruleConnected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair) ≤
      xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (level + 1) := by
  letI := xiLevelMetricSpace system ruleConnected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) level
  letI := xiCompletion_compactSpace system ruleConnected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair
  letI : Nonempty (XiVtx system level) := ⟨by simpa only [Nat.zero_add] using xiLiftVertices system 0 level true⟩
  letI : Nonempty (XiMetricCompletion system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) :=
    ⟨xiCompletionEmbedding system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair level (by simpa only [Nat.zero_add] using xiLiftVertices system 0 level true)⟩
  have comparison := ghDist_le_hausdorffDist
    (xiCompletionEmbedding_isometry system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair level)
    (isometry_id : Isometry (id : XiMetricCompletion system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair → _))
  rw [range_id] at comparison
  exact comparison.trans (xiFiniteLevel_hausdorffDist_le system ruleConnected lengths lengthsPositive
    rate rateGreaterThanOne eigenpair level)

theorem xiFiniteLevel_ghDist_tendsto_zero :
    letI : ∀ level, MetricSpace (XiVtx system level) := fun level =>
      xiLevelMetricSpace system ruleConnected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) level
    letI : ∀ level, Nonempty (XiVtx system level) := fun level =>
      ⟨by simpa only [Nat.zero_add] using xiLiftVertices system 0 level true⟩
    letI := xiCompletion_compactSpace system ruleConnected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair
    letI : Nonempty (XiMetricCompletion system ruleConnected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair) :=
      ⟨xiCompletionEmbedding system ruleConnected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair 0 true⟩
    Tendsto (fun level => ghDist (XiVtx system level)
      (XiMetricCompletion system ruleConnected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair)) atTop (nhds 0) := by
  letI : ∀ level, MetricSpace (XiVtx system level) := fun level =>
    xiLevelMetricSpace system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) level
  letI : ∀ level, Nonempty (XiVtx system level) := fun level =>
    ⟨by simpa only [Nat.zero_add] using xiLiftVertices system 0 level true⟩
  letI := xiCompletion_compactSpace system ruleConnected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair
  letI : Nonempty (XiMetricCompletion system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) :=
    ⟨xiCompletionEmbedding system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair 0 true⟩
  exact squeeze_zero (fun _ => dist_nonneg)
    (xiFiniteLevel_ghDist_le system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair)
    (xiFiniteNetRadius_tendsto_zero system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair)

end EIGS

#print axioms EIGS.xiCompletion_finite_net
#print axioms EIGS.xiFiniteLevel_hausdorffDist_le
#print axioms EIGS.xiFiniteLevel_hausdorffDist_tendsto_zero
#print axioms EIGS.xiFiniteLevel_ghDist_le
#print axioms EIGS.xiFiniteLevel_ghDist_tendsto_zero
