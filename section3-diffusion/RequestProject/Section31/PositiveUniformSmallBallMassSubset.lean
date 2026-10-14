import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

/-! A positive outer-measure subset with an estimate at every small
radius. Measurability of the subset is unnecessary: the finite covering
mass comparison uses only monotonicity and finite subadditivity. -/

namespace IGS.Sec31
open MeasureTheory Filter Set
open scoped Classical
noncomputable section

variable {Space : Type*} [MetricSpace Space] [MeasurableSpace Space]

theorem exists_positive_uniform_small_ball_mass_subset
    (physicalMeasure : Measure Space) [IsProbabilityMeasure physicalMeasure]
    (profile : ℝ → ℝ) (profileNonnegative : ∀ radius : ℝ, 0 < radius → 0 ≤ profile radius)
    (almostEverywhere : ∀ᵐ point ∂physicalMeasure, ∃ coefficient threshold : ℝ,
      0 < coefficient ∧ 0 < threshold ∧ ∀ radius : ℝ, 0 < radius → radius ≤ threshold →
        physicalMeasure.real (Metric.ball point radius) ≤ coefficient * profile radius) :
    ∃ coefficient threshold : ℝ, 0 < coefficient ∧ 0 < threshold ∧
      0 < physicalMeasure {point : Space | ∀ radius : ℝ, 0 < radius → radius ≤ threshold →
        physicalMeasure.real (Metric.ball point radius) ≤ coefficient * profile radius} := by
  let good := fun coefficient threshold : ℕ => {point : Space | ∀ radius : ℝ,
    0 < radius → radius ≤ 1 / (threshold + 1 : ℝ) →
      physicalMeasure.real (Metric.ball point radius) ≤ (coefficient + 1 : ℝ) * profile radius}
  have covered : ∀ᵐ point ∂physicalMeasure, ∃ coefficient threshold : ℕ,
      point ∈ good coefficient threshold := by
    filter_upwards [almostEverywhere] with point property
    obtain ⟨coefficient, threshold, coefficientPositive, thresholdPositive, bound⟩ := property
    obtain ⟨integerCoefficient, coefficientLarger⟩ := exists_nat_gt coefficient
    obtain ⟨integerThreshold, inverseLarger⟩ := exists_nat_gt (1 / threshold)
    have thresholdBound : 1 / (integerThreshold + 1 : ℝ) ≤ threshold := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < integerThreshold + 1)).mpr
      have productBound := (div_lt_iff₀ thresholdPositive).mp inverseLarger
      nlinarith
    refine ⟨integerCoefficient, integerThreshold, ?_⟩
    intro radius radiusPositive radiusSmall
    exact (bound radius radiusPositive (radiusSmall.trans thresholdBound)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (profileNonnegative radius radiusPositive))
  by_contra noPositive
  have nullGood (coefficient threshold : ℕ) : physicalMeasure (good coefficient threshold) = 0 := by
    by_contra nonzero
    exact noPositive ⟨(coefficient + 1 : ℝ), 1 / (threshold + 1 : ℝ), by positivity,
      by positivity, pos_iff_ne_zero.mpr nonzero⟩
  have unionNull : physicalMeasure (⋃ coefficient : ℕ, ⋃ threshold : ℕ, good coefficient threshold) = 0 :=
    measure_iUnion_null (fun coefficient => measure_iUnion_null (nullGood coefficient))
  have unionFull : ∀ᵐ point ∂physicalMeasure,
      point ∈ ⋃ coefficient : ℕ, ⋃ threshold : ℕ, good coefficient threshold := by
    filter_upwards [covered] with point property
    obtain ⟨coefficient, threshold, membership⟩ := property
    exact Set.mem_iUnion.mpr ⟨coefficient, Set.mem_iUnion.mpr ⟨threshold, membership⟩⟩
  have complementNull :
      physicalMeasure (⋃ coefficient : ℕ, ⋃ threshold : ℕ, good coefficient threshold)ᶜ = 0 := by
    simpa only [ae_iff] using unionFull
  have universeNull : physicalMeasure Set.univ = 0 := by
    rw [← Set.union_compl_self (⋃ coefficient : ℕ, ⋃ threshold : ℕ, good coefficient threshold)]
    exact measure_union_null unionNull complementNull
  norm_num at universeNull

end
end IGS.Sec31

#print axioms IGS.Sec31.exists_positive_uniform_small_ball_mass_subset
