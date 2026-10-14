import RequestProject.Section31.MetricBallMassMeasurable
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Extract a positive-mass measurable subset with a uniform eventual
ball estimate from the actual almost-everywhere, nonuniform estimate. -/

namespace IGS.Sec31
open MeasureTheory Filter Topology Set
open scoped Classical
noncomputable section

variable {Space : Type*} [MetricSpace Space] [SecondCountableTopology Space]
    [MeasurableSpace Space] [BorelSpace Space]

theorem exists_positive_uniform_eventual_ball_mass_subset
    (physicalMeasure : Measure Space) [IsProbabilityMeasure physicalMeasure]
    (radii bounds : ℕ → ℝ)
    (almostEverywhere : ∀ᵐ point ∂physicalMeasure, ∃ coefficient threshold : ℕ,
      ∀ level : ℕ, threshold ≤ level →
        physicalMeasure.real (Metric.ball point (radii level)) ≤ (coefficient + 1 : ℝ) * bounds level) :
    ∃ coefficient threshold : ℕ,
      MeasurableSet {point : Space | ∀ level : ℕ, threshold ≤ level →
        physicalMeasure.real (Metric.ball point (radii level)) ≤ (coefficient + 1 : ℝ) * bounds level} ∧
      0 < physicalMeasure {point : Space | ∀ level : ℕ, threshold ≤ level →
        physicalMeasure.real (Metric.ball point (radii level)) ≤ (coefficient + 1 : ℝ) * bounds level} := by
  let good := fun coefficient threshold : ℕ => {point : Space | ∀ level : ℕ, threshold ≤ level →
    physicalMeasure.real (Metric.ball point (radii level)) ≤ (coefficient + 1 : ℝ) * bounds level}
  have goodMeasurable (coefficient threshold : ℕ) : MeasurableSet (good coefficient threshold) := by
    simp only [good, Set.setOf_forall]
    apply MeasurableSet.iInter
    intro level
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_le (measurable_real_ball_mass physicalMeasure (radii level)) measurable_const
  by_contra noPositive
  have goodNull (coefficient threshold : ℕ) : physicalMeasure (good coefficient threshold) = 0 := by
    by_contra notZero
    exact noPositive ⟨coefficient, threshold, goodMeasurable coefficient threshold,
      pos_iff_ne_zero.mpr notZero⟩
  have unionNull : physicalMeasure (⋃ coefficient : ℕ, ⋃ threshold : ℕ, good coefficient threshold) = 0 :=
    measure_iUnion_null (fun coefficient => measure_iUnion_null (goodNull coefficient))
  have unionFull : ∀ᵐ point ∂physicalMeasure,
      point ∈ ⋃ coefficient : ℕ, ⋃ threshold : ℕ, good coefficient threshold := by
    filter_upwards [almostEverywhere] with point property
    obtain ⟨coefficient, threshold, bounds⟩ := property
    exact Set.mem_iUnion.mpr ⟨coefficient, Set.mem_iUnion.mpr ⟨threshold, bounds⟩⟩
  have complementNull :
      physicalMeasure (⋃ coefficient : ℕ, ⋃ threshold : ℕ, good coefficient threshold)ᶜ = 0 := by
    simpa only [ae_iff] using unionFull
  have universeNull : physicalMeasure Set.univ = 0 := by
    rw [← Set.union_compl_self (⋃ coefficient : ℕ, ⋃ threshold : ℕ, good coefficient threshold)]
    exact measure_union_null unionNull complementNull
  norm_num at universeNull

theorem exists_positive_uniform_ball_mass_subset_of_ae_small_radius_bound
    (physicalMeasure : Measure Space) [IsProbabilityMeasure physicalMeasure]
    (radii : ℕ → ℝ) (radiiPositive : ∀ level, 0 < radii level)
    (radiiTendsto : Tendsto radii atTop (nhds 0)) (profile : ℝ → ℝ)
    (profileNonnegative : ∀ level, 0 ≤ profile (radii level))
    (almostEverywhere : ∀ᵐ point ∂physicalMeasure, ∃ coefficient threshold : ℝ,
      0 < coefficient ∧ 0 < threshold ∧ ∀ radius : ℝ, 0 < radius → radius ≤ threshold →
        physicalMeasure.real (Metric.ball point radius) ≤ coefficient * profile radius) :
    ∃ coefficient threshold : ℕ,
      MeasurableSet {point : Space | ∀ level : ℕ, threshold ≤ level →
        physicalMeasure.real (Metric.ball point (radii level)) ≤
          (coefficient + 1 : ℝ) * profile (radii level)} ∧
      0 < physicalMeasure {point : Space | ∀ level : ℕ, threshold ≤ level →
        physicalMeasure.real (Metric.ball point (radii level)) ≤
          (coefficient + 1 : ℝ) * profile (radii level)} := by
  apply exists_positive_uniform_eventual_ball_mass_subset physicalMeasure radii (fun level => profile (radii level))
  filter_upwards [almostEverywhere] with point property
  obtain ⟨coefficient, threshold, coefficientPositive, thresholdPositive, bound⟩ := property
  obtain ⟨integerCoefficient, larger⟩ := exists_nat_gt coefficient
  have smallRadii : ∀ᶠ level in atTop, radii level < threshold :=
    radiiTendsto.eventually (gt_mem_nhds thresholdPositive)
  obtain ⟨integerThreshold, after⟩ := Filter.eventually_atTop.mp smallRadii
  refine ⟨integerCoefficient, integerThreshold, ?_⟩
  intro level large
  have actualBound := bound (radii level) (radiiPositive level) (after level large).le
  exact actualBound.trans (mul_le_mul_of_nonneg_right (by linarith)
    (profileNonnegative level))

end
end IGS.Sec31

#print axioms IGS.Sec31.exists_positive_uniform_eventual_ball_mass_subset
#print axioms IGS.Sec31.exists_positive_uniform_ball_mass_subset_of_ae_small_radius_bound
