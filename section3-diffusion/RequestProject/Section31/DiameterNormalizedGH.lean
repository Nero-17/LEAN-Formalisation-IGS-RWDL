import RequestProject.Section31.PositiveScaledMetric

/-! A quantitative GH bound after diameter normalization. All approximation
and diameter hypotheses will be discharged for the original Xi graphs. -/

namespace EIGS

open Metric Set GromovHausdorff

noncomputable def diameterNormalizedGHPoint (Space : Type*) [MetricSpace Space]
    [CompactSpace Space] [Nonempty Space] (diameterPositive : 0 < Metric.diam (univ : Set Space)) : GHSpace :=
  letI := positiveScaledMetricSpace Space (Metric.diam (univ : Set Space))⁻¹ (inv_pos.mpr diameterPositive)
  toGHSpace Space

theorem diameterNormalizedGHPoint_dist_le {First Second : Type*}
    [firstMetric : MetricSpace First] [secondMetric : MetricSpace Second]
    [CompactSpace First] [CompactSpace Second] [Nonempty First] [Nonempty Second]
    (firstDiameterPositive : 0 < Metric.diam (univ : Set First))
    (secondDiameterPositive : 0 < Metric.diam (univ : Set Second))
    (embedding : First → Second) (distanceError diameterError mesh : ℝ)
    (distanceErrorNonnegative : 0 ≤ distanceError) (diameterErrorNonnegative : 0 ≤ diameterError)
    (diameterLower : Metric.diam (univ : Set Second) / 2 ≤ Metric.diam (univ : Set First))
    (distortion : ∀ source sink,
      |dist source sink - dist (embedding source) (embedding sink)| ≤ distanceError)
    (diameterBound : |Metric.diam (univ : Set First) - Metric.diam (univ : Set Second)| ≤ diameterError)
    (net : ∀ point : Second, ∃ vertex : First, dist point (embedding vertex) ≤ mesh) :
    dist (diameterNormalizedGHPoint First firstDiameterPositive)
      (diameterNormalizedGHPoint Second secondDiameterPositive) ≤
        (distanceError + diameterError) / Metric.diam (univ : Set Second) +
          mesh / Metric.diam (univ : Set Second) := by
  have normalizedDistortion : ∀ source sink,
      |dist source sink / Metric.diam (univ : Set First) -
        dist (embedding source) (embedding sink) / Metric.diam (univ : Set Second)| ≤
      2 * (distanceError + diameterError) / Metric.diam (univ : Set Second) := by
    intro source sink
    exact normalized_distance_error_le secondDiameterPositive diameterLower dist_nonneg
      (Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _))
      distanceErrorNonnegative diameterErrorNonnegative (distortion source sink) diameterBound
  letI := positiveScaledMetricSpace First (Metric.diam (univ : Set First))⁻¹ (inv_pos.mpr firstDiameterPositive)
  letI := positiveScaledMetricSpace Second
    (@Metric.diam Second secondMetric.toPseudoMetricSpace univ)⁻¹ (inv_pos.mpr secondDiameterPositive)
  have comparison := ghDist_le_of_approx_subsets
    (s := (univ : Set First)) (fun vertex => embedding vertex.val)
    (ε₁ := 0)
    (ε₂ := 2 * (distanceError + diameterError) / @Metric.diam Second secondMetric.toPseudoMetricSpace univ)
    (ε₃ := mesh / @Metric.diam Second secondMetric.toPseudoMetricSpace univ)
    (fun vertex => ⟨vertex, mem_univ _, by simp only [dist_self, le_refl]⟩)
    (fun point => by
      obtain ⟨vertex, bound⟩ := net point
      refine ⟨⟨vertex, mem_univ _⟩, ?_⟩
      change (@Metric.diam Second secondMetric.toPseudoMetricSpace univ)⁻¹ *
        @dist Second secondMetric.toDist point (embedding vertex) ≤ _
      simpa only [div_eq_mul_inv, mul_comm] using
        mul_le_mul_of_nonneg_left bound (inv_nonneg.mpr secondDiameterPositive.le))
    (fun first second => by
      change |(@Metric.diam First firstMetric.toPseudoMetricSpace univ)⁻¹ *
        @dist First firstMetric.toDist first.val second.val -
        (@Metric.diam Second secondMetric.toPseudoMetricSpace univ)⁻¹ *
        @dist Second secondMetric.toDist (embedding first.val) (embedding second.val)| ≤ _
      simpa only [div_eq_mul_inv, mul_comm] using normalizedDistortion first.val second.val)
  change ghDist First Second ≤ _
  calc
    _ ≤ 0 + (2 * (distanceError + diameterError) /
        @Metric.diam Second secondMetric.toPseudoMetricSpace univ) / 2 +
        mesh / @Metric.diam Second secondMetric.toPseudoMetricSpace univ := comparison
    _ = _ := by ring

end EIGS

#print axioms EIGS.diameterNormalizedGHPoint_dist_le
