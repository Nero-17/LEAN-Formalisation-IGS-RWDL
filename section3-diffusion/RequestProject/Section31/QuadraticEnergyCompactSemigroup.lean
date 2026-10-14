import RequestProject.Section31.QuadraticEnergyFiniteApproximation
import RequestProject.Section31.QuadraticEnergySemigroupSmoothing

/-! Compact bounded-energy balls and the proved positive-time energy bound
give compactness of the actually constructed closed L² semigroup. -/

namespace IGS.Sec31.QuadraticEnergySpace

open Filter Topology
open scoped NNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem closedSemigroup_compact_of_compact_energy_balls
    (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set H))
    (compactBalls : ∀ normBound energyBound : ℝ, 0 ≤ energyBound →
      IsCompact (closedEnergyBoundedBall domain form nonnegative closable normBound energyBound))
    (time : ℝ≥0) (timePositive : 0 < time) :
    IsCompactOperator (closedSemigroup domain form nonnegative closable domainDense time) := by
  let operator := closedSemigroup domain form nonnegative closable domainDense time
  have denominatorPositive : 0 < 2 * (time : ℝ) := mul_pos (by norm_num) timePositive
  apply (isCompactOperator_iff_image_closedBall_subset_compact operator.toLinearMap zero_lt_one).mpr
  refine ⟨closedEnergyBoundedBall domain form nonnegative closable 1 (1 / (2 * (time : ℝ))),
    compactBalls _ _ (by positivity), ?_⟩
  rintro _ ⟨values, valuesBounded, rfl⟩
  have normBounded : ‖values‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using valuesBounded
  obtain ⟨lifted, liftedEquality, liftedEnergy⟩ :=
    closedSemigroup_exists_energy_bound domain form nonnegative closable domainDense time timePositive values
  refine ⟨?_, lifted, liftedEquality, ?_⟩
  · exact ((operator.le_of_opNorm_le
      (closedSemigroup_norm domain form nonnegative closable domainDense time) values).trans
        (by simpa only [one_mul] using normBounded))
  · apply liftedEnergy.trans
    apply div_le_div_of_nonneg_right _ denominatorPositive.le
    nlinarith [norm_nonneg values]

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_compact_of_compact_energy_balls
