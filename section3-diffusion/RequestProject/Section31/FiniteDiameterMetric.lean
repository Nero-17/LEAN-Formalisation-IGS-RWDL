import RequestProject.Section31.DiameterNormalizedScale

/-! A metric-parametrized normalization for finite spaces. The zero-diameter
branch only makes transport across equal metric structures nondependent;
all graph applications establish strict positivity before using it. -/

namespace EIGS

open Metric Set GromovHausdorff

noncomputable def finiteDiameterMetricPoint (Space : Type*) [Finite Space] [Nonempty Space]
    (metric : MetricSpace Space) : GHSpace :=
  letI := metric
  if diameterPositive : 0 < Metric.diam (univ : Set Space) then
    diameterNormalizedGHPoint Space diameterPositive
  else toGHSpace Space

theorem finiteDiameterMetricPoint_eq (Space : Type*) [Finite Space] [Nonempty Space]
    (metric : MetricSpace Space)
    (diameterPositive : 0 < @Metric.diam Space metric.toPseudoMetricSpace univ) :
    finiteDiameterMetricPoint Space metric =
      @diameterNormalizedGHPoint Space metric (by infer_instance) (by infer_instance) diameterPositive := by
  exact dif_pos diameterPositive

theorem finiteDiameterMetricPoint_scale_invariant (Space : Type*) [Finite Space] [Nonempty Space]
    [metric : MetricSpace Space] (diameterPositive : 0 < Metric.diam (univ : Set Space))
    (scale : ℝ) (scalePositive : 0 < scale) :
    finiteDiameterMetricPoint Space (positiveScaledMetricSpace Space scale scalePositive) =
      finiteDiameterMetricPoint Space metric := by
  have scaledDiameterPositive : 0 < @Metric.diam Space
      (positiveScaledMetricSpace Space scale scalePositive).toPseudoMetricSpace univ := by
    rw [positiveScaledMetricSpace_diameter]
    exact mul_pos scalePositive diameterPositive
  rw [finiteDiameterMetricPoint_eq Space _ scaledDiameterPositive,
    finiteDiameterMetricPoint_eq Space _ diameterPositive]
  exact diameterNormalizedGHPoint_scale_invariant Space diameterPositive scale scalePositive

end EIGS

#print axioms EIGS.finiteDiameterMetricPoint_scale_invariant
