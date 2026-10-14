import RequestProject.Section31.EIGSOriginalMeasuredGHP

/-! The actual positive rescaling used by diameter normalization retains
the original topology definitionally. The identity homeomorph is therefore
constructed without assuming equality of distances, an external metric
comparison, or an independent topological identification. -/

namespace EIGS
noncomputable section
open Metric Set

def positiveScaledIdentityHomeomorph (Space : Type*) [original : MetricSpace Space]
    (scale : ℝ) (scalePositive : 0 < scale) :
    @Homeomorph Space Space original.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (positiveScaledMetricSpace Space scale scalePositive).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace :=
  Homeomorph.refl Space

theorem positiveScaledIdentityHomeomorph_apply (Space : Type*) [MetricSpace Space]
    (scale : ℝ) (scalePositive : 0 < scale) (point : Space) :
    positiveScaledIdentityHomeomorph Space scale scalePositive point = point := rfl

namespace MeasuredGHP

def diameterNormalizationHomeomorph (Space : Type) [original : MetricSpace Space]
    (diameterPositive : 0 < Metric.diam (univ : Set Space)) :
    @Homeomorph Space Space original.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (normalizedMetric Space original diameterPositive).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace :=
  positiveScaledIdentityHomeomorph Space (Metric.diam (univ : Set Space))⁻¹ (inv_pos.mpr diameterPositive)

theorem diameterNormalizationHomeomorph_apply (Space : Type) [MetricSpace Space]
    (diameterPositive : 0 < Metric.diam (univ : Set Space)) (point : Space) :
    diameterNormalizationHomeomorph Space diameterPositive point = point := rfl

theorem diameterNormalized_dist_exact (Space : Type) [original : MetricSpace Space]
    (diameterPositive : 0 < Metric.diam (univ : Set Space)) (first second : Space) :
    @dist Space (normalizedMetric Space original diameterPositive).toDist first second =
      dist first second / Metric.diam (univ : Set Space) := by
  change (Metric.diam (univ : Set Space))⁻¹ * dist first second = _
  rw [div_eq_mul_inv, mul_comm]

end MeasuredGHP
end
end EIGS

#print axioms EIGS.positiveScaledIdentityHomeomorph
#print axioms EIGS.MeasuredGHP.diameterNormalizationHomeomorph
#print axioms EIGS.MeasuredGHP.diameterNormalized_dist_exact
