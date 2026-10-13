import Mathlib.Topology.MetricSpace.GromovHausdorff

/-! Positive scalar multiplication of a metric, preserving the original
topology definitionally. This will be used for diameter normalization. -/

namespace EIGS

open Metric Set

noncomputable def positiveScaledMetricSpace (Space : Type*) [MetricSpace Space]
    (scale : ℝ) (scalePositive : 0 < scale) : MetricSpace Space :=
  MetricSpace.ofDistTopology (fun source sink => scale * dist source sink)
    (by intro point; simp only [dist_self, mul_zero])
    (by intro source sink; exact congrArg (scale * ·) (dist_comm source sink))
    (by intro source middle sink; simpa only [mul_add] using
      mul_le_mul_of_nonneg_left (dist_triangle source middle sink) scalePositive.le)
    (by
      intro subset
      constructor
      · intro subsetOpen point pointMem
        obtain ⟨radius, radiusPositive, radiusBound⟩ := Metric.isOpen_iff.mp subsetOpen point pointMem
        refine ⟨scale * radius, mul_pos scalePositive radiusPositive, ?_⟩
        intro other bound
        apply radiusBound
        change dist other point < radius
        rw [dist_comm]
        exact (mul_lt_mul_iff_right₀ scalePositive).mp bound
      · intro subsetOpen
        apply Metric.isOpen_iff.mpr
        intro point pointMem
        obtain ⟨radius, radiusPositive, radiusBound⟩ := subsetOpen point pointMem
        refine ⟨radius / scale, div_pos radiusPositive scalePositive, ?_⟩
        intro other bound
        apply radiusBound other
        change scale * dist point other < radius
        simpa only [mul_comm, dist_comm] using (lt_div_iff₀ scalePositive).mp bound)
    (by
      intro source sink distanceZero
      exact eq_of_dist_eq_zero ((mul_eq_zero.mp distanceZero).resolve_left scalePositive.ne'))

theorem positiveScaledMetricSpace_diameter (Space : Type*) [original : MetricSpace Space]
    [CompactSpace Space] (scale : ℝ) (scalePositive : 0 < scale) :
    letI := positiveScaledMetricSpace Space scale scalePositive
    Metric.diam (univ : Set Space) =
      scale * @Metric.diam Space original.toPseudoMetricSpace univ := by
  have originalBounded := (isCompact_univ : IsCompact (univ : Set Space)).isBounded
  have originalDiameterNonnegative : 0 ≤ @Metric.diam Space original.toPseudoMetricSpace univ :=
    Metric.diam_nonneg
  letI := positiveScaledMetricSpace Space scale scalePositive
  have forward : Metric.diam (univ : Set Space) ≤
      scale * @Metric.diam Space original.toPseudoMetricSpace univ := by
    apply Metric.diam_le_of_forall_dist_le (mul_nonneg scalePositive.le originalDiameterNonnegative)
    intro source _ sink _
    change scale * @dist Space original.toDist source sink ≤ _
    have originalPairBound : @dist Space original.toDist source sink ≤
        @Metric.diam Space original.toPseudoMetricSpace univ := by
      letI := original
      exact Metric.dist_le_diam_of_mem originalBounded (mem_univ source) (mem_univ sink)
    exact mul_le_mul_of_nonneg_left originalPairBound scalePositive.le
  have scaledDiameterNonnegative : 0 ≤ Metric.diam (univ : Set Space) := Metric.diam_nonneg
  have scaledBound : ∀ source sink : Space,
      scale * @dist Space original.toDist source sink ≤ Metric.diam (univ : Set Space) := by
    intro source sink
    exact Metric.dist_le_diam_of_mem (isCompact_univ : IsCompact (univ : Set Space)).isBounded
      (mem_univ source) (mem_univ sink)
  have backward : @Metric.diam Space original.toPseudoMetricSpace univ ≤
      Metric.diam (univ : Set Space) / scale := by
    letI := original
    apply Metric.diam_le_of_forall_dist_le (div_nonneg scaledDiameterNonnegative scalePositive.le)
    intro source _ sink _
    exact (le_div_iff₀ scalePositive).mpr (by simpa only [mul_comm] using scaledBound source sink)
  exact le_antisymm forward (by
    have := (le_div_iff₀ scalePositive).mp backward
    simpa only [mul_comm] using this)

theorem normalized_distance_error_le {firstDistance secondDistance firstDiameter secondDiameter
    distanceError diameterError : ℝ}
    (secondDiameterPositive : 0 < secondDiameter)
    (diameterLower : secondDiameter / 2 ≤ firstDiameter)
    (distanceNonnegative : 0 ≤ secondDistance) (distanceBound : secondDistance ≤ secondDiameter)
    (distanceErrorNonnegative : 0 ≤ distanceError) (diameterErrorNonnegative : 0 ≤ diameterError)
    (firstError : |firstDistance - secondDistance| ≤ distanceError)
    (secondError : |firstDiameter - secondDiameter| ≤ diameterError) :
    |firstDistance / firstDiameter - secondDistance / secondDiameter| ≤
      2 * (distanceError + diameterError) / secondDiameter := by
  have firstDiameterPositive : 0 < firstDiameter := (half_pos secondDiameterPositive).trans_le diameterLower
  have numeratorBound : |firstDistance * secondDiameter - secondDistance * firstDiameter| ≤
      secondDiameter * (distanceError + diameterError) := by
    calc
      _ = |secondDiameter * (firstDistance - secondDistance) +
          secondDistance * (secondDiameter - firstDiameter)| := by congr 1 <;> ring
      _ ≤ |secondDiameter * (firstDistance - secondDistance)| +
          |secondDistance * (secondDiameter - firstDiameter)| := abs_add_le _ _
      _ = secondDiameter * |firstDistance - secondDistance| +
          secondDistance * |firstDiameter - secondDiameter| := by
        rw [abs_mul, abs_mul, abs_of_pos secondDiameterPositive,
          abs_of_nonneg distanceNonnegative, abs_sub_comm secondDiameter firstDiameter]
      _ ≤ secondDiameter * distanceError + secondDistance * diameterError :=
        add_le_add (mul_le_mul_of_nonneg_left firstError secondDiameterPositive.le)
          (mul_le_mul_of_nonneg_left secondError distanceNonnegative)
      _ ≤ secondDiameter * (distanceError + diameterError) := by
        nlinarith only [mul_le_mul_of_nonneg_right distanceBound diameterErrorNonnegative]
  have identity : firstDistance / firstDiameter - secondDistance / secondDiameter =
      (firstDistance * secondDiameter - secondDistance * firstDiameter) /
        (firstDiameter * secondDiameter) := by field_simp <;> ring
  rw [identity, abs_div, abs_of_pos (mul_pos firstDiameterPositive secondDiameterPositive)]
  apply (div_le_iff₀ (mul_pos firstDiameterPositive secondDiameterPositive)).mpr
  calc
    _ ≤ secondDiameter * (distanceError + diameterError) := numeratorBound
    _ ≤ 2 * (distanceError + diameterError) * firstDiameter := by
      nlinarith only [mul_le_mul_of_nonneg_right diameterLower
        (add_nonneg distanceErrorNonnegative diameterErrorNonnegative)]
    _ = 2 * (distanceError + diameterError) / secondDiameter * (firstDiameter * secondDiameter) := by
      field_simp <;> ring

end EIGS

#print axioms EIGS.positiveScaledMetricSpace_diameter
#print axioms EIGS.normalized_distance_error_le
