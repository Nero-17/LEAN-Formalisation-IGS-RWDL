import RequestProject.Section31.EIGSUnitGromovHausdorff

/-! Diameter controls for the actual finite nets, including the error caused
by replacing one finite metric by another on the same vertex set. -/

namespace EIGS

open Filter Topology Metric Set

private theorem finite_diameter_le_of_distance_bound {Vertex : Type*} [Finite Vertex]
    (first second : MetricSpace Vertex) {tolerance : ℝ} (toleranceNonnegative : 0 ≤ tolerance)
    (bound : ∀ source sink,
      @dist Vertex first.toDist source sink ≤ @dist Vertex second.toDist source sink + tolerance) :
    @Metric.diam Vertex first.toPseudoMetricSpace univ ≤
      @Metric.diam Vertex second.toPseudoMetricSpace univ + tolerance := by
  letI := first
  have secondDiameterNonnegative : 0 ≤ @Metric.diam Vertex second.toPseudoMetricSpace univ := by
    letI := second
    exact Metric.diam_nonneg
  apply Metric.diam_le_of_forall_dist_le
    (add_nonneg secondDiameterNonnegative toleranceNonnegative)
  intro source _ sink _
  have secondBound : @dist Vertex second.toDist source sink ≤
      @Metric.diam Vertex second.toPseudoMetricSpace univ := by
    letI := second
    exact Metric.dist_le_diam_of_mem (Set.finite_univ.isBounded) (mem_univ _) (mem_univ _)
  linarith only [bound source sink, secondBound]

theorem finite_diameter_distortion_le {Vertex : Type*} [Finite Vertex]
    (first second : MetricSpace Vertex) {tolerance : ℝ} (toleranceNonnegative : 0 ≤ tolerance)
    (bound : ∀ source sink,
      |@dist Vertex first.toDist source sink - @dist Vertex second.toDist source sink| ≤ tolerance) :
    |@Metric.diam Vertex first.toPseudoMetricSpace univ -
      @Metric.diam Vertex second.toPseudoMetricSpace univ| ≤ tolerance := by
  have forward := finite_diameter_le_of_distance_bound first second toleranceNonnegative
    (fun source sink => by have := (abs_le.mp (bound source sink)).2; linarith)
  have backward := finite_diameter_le_of_distance_bound second first toleranceNonnegative
    (fun source sink => by have := (abs_le.mp (bound source sink)).1; linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

variable {K : ℕ} (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)

theorem xiFiniteLevel_diameter_error_le (level : ℕ) :
    letI := xiLevelMetricSpace system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) level
    |Metric.diam (univ : Set (XiVtx system level)) -
      Metric.diam (univ : Set (XiMetricCompletion system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair))| ≤
      2 * (xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (level + 1)) := by
  letI := xiLevelMetricSpace system connected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) level
  letI := xiCompletion_compactSpace system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
  have radiusNonnegative : 0 ≤ xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (level + 1) := by
    exact mul_nonneg
      (div_nonneg (xiRuleRadius_nonnegative system (fun colour => (lengthsPositive colour).le))
        (sub_pos.mpr ((inv_lt_one₀ (zero_lt_one.trans rateGreaterThanOne)).mpr rateGreaterThanOne)).le)
      (pow_nonneg (inv_nonneg.mpr (zero_le_one.trans rateGreaterThanOne.le)) _)
  have forward : Metric.diam (univ : Set (XiVtx system level)) ≤
      Metric.diam (univ : Set (XiMetricCompletion system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair)) := by
    apply Metric.diam_le_of_forall_dist_le Metric.diam_nonneg
    intro source _ sink _
    rw [← (xiCompletionEmbedding_isometry system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair level).dist_eq source sink]
    exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)
  have backward : Metric.diam (univ : Set (XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair)) ≤
      Metric.diam (univ : Set (XiVtx system level)) +
        2 * (xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (level + 1)) := by
    apply Metric.diam_le_of_forall_dist_le (add_nonneg Metric.diam_nonneg (mul_nonneg (by norm_num) radiusNonnegative))
    intro source _ sink _
    obtain ⟨first, firstBound⟩ := xiCompletion_finite_net system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair level source
    obtain ⟨second, secondBound⟩ := xiCompletion_finite_net system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair level sink
    have finiteBound := Metric.dist_le_diam_of_mem (Set.finite_univ.isBounded)
      (mem_univ first) (mem_univ second)
    have triangle := dist_triangle source
      (xiCompletionEmbedding system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair level first) sink
    have middleTriangle := dist_triangle
      (xiCompletionEmbedding system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair level first)
      (xiCompletionEmbedding system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair level second) sink
    rw [(xiCompletionEmbedding_isometry system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair level).dist_eq,
      dist_comm (xiCompletionEmbedding system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair level second) sink] at middleTriangle
    linarith only [triangle, middleTriangle, firstBound, secondBound, finiteBound]
  exact abs_le.mpr ⟨by linarith only [backward], by linarith only [forward, radiusNonnegative]⟩

end EIGS

#print axioms EIGS.finite_diameter_distortion_le
#print axioms EIGS.xiFiniteLevel_diameter_error_le
