import RequestProject.Section31.ContinuousMetricBallCutoff
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Passing a maximal displacement probability to a continuous distance-test
expectation. The source may lie anywhere in the inner radius around the
desired limit point. This does not identify a continuum transition event.
Candidate source: no compilation is claimed. -/

namespace IGS.Sec31
open MeasureTheory
open scoped Topology Classical
noncomputable section

theorem integral_test_ge_one_sub_bad_probability {Sample : Type*}
    [MeasurableSpace Sample] (law : Measure Sample) [IsProbabilityMeasure law]
    (bad : Set Sample) (badMeasurable : MeasurableSet bad)
    (test : Sample → ℝ) (testIntegrable : Integrable test law)
    (testNonnegative : ∀ᵐ sample ∂law, 0 ≤ test sample)
    (testOne : ∀ᵐ sample ∂law, sample ∉ bad → test sample = 1) :
    1 - law.real bad ≤ ∫ sample, test sample ∂law := by
  have indicatorIntegrable : Integrable (bad.indicator (fun _ : Sample => (1 : ℝ))) law :=
    (integrable_const (1 : ℝ)).indicator badMeasurable
  have comparison : ∀ᵐ sample ∂law,
      1 - bad.indicator (fun _ : Sample => (1 : ℝ)) sample ≤ test sample := by
    filter_upwards [testNonnegative, testOne] with sample nonnegative oneOutside
    by_cases inside : sample ∈ bad
    · simpa only [Set.indicator_of_mem inside, sub_self] using nonnegative
    · simp only [Set.indicator_of_notMem inside, sub_zero, oneOutside inside, le_refl]
  have compared := integral_mono_ae
    ((integrable_const (1 : ℝ)).sub indicatorIntegrable) testIntegrable comparison
  change (∫ sample, (1 : ℝ) - bad.indicator (fun _ : Sample => (1 : ℝ)) sample ∂law) ≤
    ∫ sample, test sample ∂law at compared
  rw [integral_sub (integrable_const (1 : ℝ)) indicatorIntegrable] at compared
  have indicatorIdentity :
      (∫ sample, bad.indicator (fun _ : Sample => (1 : ℝ)) sample ∂law) = law.real bad := by
    simpa only [smul_eq_mul, mul_one] using
      (integral_indicator_const (μ := law) (1 : ℝ) badMeasurable)
  simpa only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul,
    indicatorIdentity] using compared

theorem continuousMetricBallCutoff_integral_ge_of_displacement
    {Vertex Space : Type*} [MeasurableSpace Vertex] [MetricSpace Space]
    (law : Measure (ℕ → Vertex)) [IsProbabilityMeasure law]
    (embedding : Vertex → Space) (center : Space) (radius : ℝ)
    (radiusPositive : 0 < radius) (source : Vertex)
    (sourceNear : dist (embedding source) center ≤ radius)
    (sourceAtZero : ∀ᵐ path ∂law, path 0 = source) (horizon : ℕ)
    (bad : Set (ℕ → Vertex)) (badMeasurable : MeasurableSet bad)
    (badContains : ∀ path, radius < dist (embedding (path horizon)) (embedding (path 0)) → path ∈ bad)
    (testIntegrable : Integrable
      (fun path => continuousMetricBallCutoff center (2 * radius) (embedding (path horizon))) law) :
    1 - law.real bad ≤
      ∫ path, continuousMetricBallCutoff center (2 * radius) (embedding (path horizon)) ∂law := by
  apply integral_test_ge_one_sub_bad_probability law bad badMeasurable _ testIntegrable
  · exact Filter.Eventually.of_forall (fun path =>
      (continuousMetricBallCutoff_bounds center (embedding (path horizon)) (2 * radius)).1)
  · filter_upwards [sourceAtZero] with path startsAtSource outside
    have displacement : dist (embedding (path horizon)) (embedding (path 0)) ≤ radius := by
      by_contra tooLarge
      exact outside (badContains path (lt_of_not_ge tooLarge))
    have nearCenter : dist (embedding (path horizon)) center ≤ 2 * radius := by
      have triangle := dist_triangle (embedding (path horizon)) (embedding source) center
      rw [startsAtSource] at displacement
      linarith
    exact continuousMetricBallCutoff_eq_one center (embedding (path horizon)) (2 * radius)
      (by positivity) (Metric.mem_closedBall.mpr nearCenter)

end
end IGS.Sec31

#print axioms IGS.Sec31.integral_test_ge_one_sub_bad_probability
#print axioms IGS.Sec31.continuousMetricBallCutoff_integral_ge_of_displacement
