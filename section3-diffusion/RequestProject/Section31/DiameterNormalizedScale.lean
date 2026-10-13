import RequestProject.Section31.DiameterNormalizedGH

/-! Normalization by the actual diameter cancels any positive common scale. -/

namespace EIGS

open Metric Set GromovHausdorff

theorem diameterNormalizedGHPoint_scale_invariant (Space : Type*) [original : MetricSpace Space]
    [compact : CompactSpace Space] [nonempty : Nonempty Space]
    (diameterPositive : 0 < Metric.diam (univ : Set Space))
    (scale : ℝ) (scalePositive : 0 < scale) :
    @diameterNormalizedGHPoint Space (positiveScaledMetricSpace Space scale scalePositive) compact nonempty
      (by
        change 0 < @Metric.diam Space (positiveScaledMetricSpace Space scale scalePositive).toPseudoMetricSpace univ
        rw [positiveScaledMetricSpace_diameter]
        exact mul_pos scalePositive diameterPositive) =
      diameterNormalizedGHPoint Space diameterPositive := by
  have scaledDiameter : @Metric.diam Space
      (positiveScaledMetricSpace Space scale scalePositive).toPseudoMetricSpace univ =
      scale * Metric.diam (univ : Set Space) := positiveScaledMetricSpace_diameter Space scale scalePositive
  have scaledDiameterPositive : 0 < @Metric.diam Space
      (positiveScaledMetricSpace Space scale scalePositive).toPseudoMetricSpace univ := by
    rw [scaledDiameter]
    exact mul_pos scalePositive diameterPositive
  have metricEquality :
      @positiveScaledMetricSpace Space (positiveScaledMetricSpace Space scale scalePositive)
        (@Metric.diam Space (positiveScaledMetricSpace Space scale scalePositive).toPseudoMetricSpace univ)⁻¹
        (inv_pos.mpr scaledDiameterPositive) =
      positiveScaledMetricSpace Space (Metric.diam (univ : Set Space))⁻¹ (inv_pos.mpr diameterPositive) := by
    apply MetricSpace.ext
    ext source sink
    change (@Metric.diam Space (positiveScaledMetricSpace Space scale scalePositive).toPseudoMetricSpace univ)⁻¹ *
      (scale * dist source sink) = (Metric.diam (univ : Set Space))⁻¹ * dist source sink
    rw [scaledDiameter, mul_inv_rev]
    field_simp
  change @toGHSpace Space
    (@positiveScaledMetricSpace Space (positiveScaledMetricSpace Space scale scalePositive)
      (@Metric.diam Space (positiveScaledMetricSpace Space scale scalePositive).toPseudoMetricSpace univ)⁻¹
      (inv_pos.mpr scaledDiameterPositive)) compact nonempty =
    @toGHSpace Space
      (positiveScaledMetricSpace Space (Metric.diam (univ : Set Space))⁻¹ (inv_pos.mpr diameterPositive)) compact nonempty
  congr 1

end EIGS

#print axioms EIGS.diameterNormalizedGHPoint_scale_invariant
