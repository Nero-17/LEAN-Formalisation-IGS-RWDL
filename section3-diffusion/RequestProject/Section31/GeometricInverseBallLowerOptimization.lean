import RequestProject.Section31.GeometricLogarithmicHeatTimeChoice
import RequestProject.Section31.NashTwoScaleOptimization
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Convert all-time geometric-scale inverse closed-ball estimates to an
inverse open-ball estimate at the continuous power radius. The geometric
estimate is an intermediate structural input; the actual consumer supplies
it from its constructed kernel and native stay bounds. Candidate source. -/

namespace IGS.Sec31
open MeasureTheory Filter Topology Metric
open scoped NNReal
noncomputable section

theorem inverse_open_ball_lower_of_geometric_closed_balls
    {Space : Type*} [MetricSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (law : Measure Space) [IsFiniteMeasure law] [law.IsOpenPosMeasure]
    (timeRate distanceRate timeScale radiusScale coefficient : ℝ)
    (timeRateGreaterThanOne : 1 < timeRate) (distanceRateGreaterThanOne : 1 < distanceRate)
    (timeScalePositive : 0 < timeScale) (radiusScalePositive : 0 < radiusScale)
    (coefficientPositive : 0 < coefficient)
    (diagonal : {time : ℝ≥0 // 0 < time} → Space → ℝ)
    (levelLower : ∀ (level : ℕ) (time : {time : ℝ≥0 // 0 < time}),
      (time.val : ℝ) ≤ timeScale * timeRate⁻¹ ^ level → ∀ point,
      coefficient / law.real (closedBall point (radiusScale * distanceRate⁻¹ ^ level)) ≤ diagonal time point) :
    ∃ radiusConstant : ℝ, 0 < radiusConstant ∧ ∃ cutoffTime : ℝ, 0 < cutoffTime ∧
      ∀ time : {time : ℝ≥0 // 0 < time}, (time.val : ℝ) ≤ cutoffTime → ∀ point,
      coefficient / law.real
        (ball point (radiusConstant * (time.val : ℝ) ^ (Real.log distanceRate / Real.log timeRate))) ≤
        diagonal time point := by
  have timeRatePositive := zero_lt_one.trans timeRateGreaterThanOne
  have distanceRatePositive := zero_lt_one.trans distanceRateGreaterThanOne
  let exponent := Real.log distanceRate / Real.log timeRate
  obtain ⟨exponentNonnegative, growthIdentity⟩ := geometric_growth_logarithmic_exponent
    timeRate distanceRate timeRateGreaterThanOne distanceRateGreaterThanOne.le
  let radiusCoefficient := radiusScale * distanceRate / timeScale ^ exponent
  have radiusCoefficientPositive : 0 < radiusCoefficient :=
    div_pos (mul_pos radiusScalePositive distanceRatePositive)
      (Real.rpow_pos_of_pos timeScalePositive exponent)
  refine ⟨2 * radiusCoefficient, by positivity, min timeScale (Real.exp (-1)),
    lt_min timeScalePositive (Real.exp_pos _), ?_⟩
  intro time timeSmall point
  have timePositive : 0 < (time.val : ℝ) := time.property
  obtain ⟨level, _, lower, upper, _⟩ := geometric_heat_time_level_with_log_bound
    timeRate timeScale (time.val : ℝ) timeRateGreaterThanOne timeScalePositive timePositive 0
    (by simpa only [pow_zero, div_one] using timeSmall.trans (min_le_left _ _))
    (timeSmall.trans (min_le_right _ _))
  have timeAtLevel : (time.val : ℝ) ≤ timeScale * timeRate⁻¹ ^ level := by
    rw [inv_pow, ← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos timeRatePositive level)).mpr
    simpa only [mul_comm] using (le_div_iff₀ timePositive).mp lower
  have nextScaleAtMostTime : timeScale / timeRate ^ (level + 1) ≤ (time.val : ℝ) := by
    apply (div_le_iff₀ (pow_pos timeRatePositive (level + 1))).mpr
    simpa only [mul_comm] using ((div_lt_iff₀ timePositive).mp upper).le
  have scalePower : (timeRate ^ (level + 1)) ^ exponent = distanceRate ^ (level + 1) := by
    rw [growthIdentity, ← Real.rpow_mul_natCast timeRatePositive.le,
      mul_comm exponent, Real.rpow_natCast_mul timeRatePositive.le]
  have radiusIdentity : radiusScale * distanceRate⁻¹ ^ level =
      radiusCoefficient * (timeScale / timeRate ^ (level + 1)) ^ exponent := by
    dsimp only [radiusCoefficient]
    rw [Real.div_rpow timeScalePositive.le (pow_nonneg timeRatePositive.le _),
      scalePower, pow_succ, inv_pow]
    field_simp [pow_ne_zero level distanceRatePositive.ne', distanceRatePositive.ne',
      (Real.rpow_pos_of_pos timeScalePositive exponent).ne']
    <;> ring
  have radiusAtMost : radiusScale * distanceRate⁻¹ ^ level ≤
      radiusCoefficient * (time.val : ℝ) ^ exponent := by
    rw [radiusIdentity]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (div_nonneg timeScalePositive.le (pow_nonneg timeRatePositive.le _))
        nextScaleAtMostTime exponentNonnegative) radiusCoefficientPositive.le
  have radiusStrict : radiusScale * distanceRate⁻¹ ^ level <
      (2 * radiusCoefficient) * (time.val : ℝ) ^ exponent := by
    have positive := mul_pos radiusCoefficientPositive (Real.rpow_pos_of_pos timePositive exponent)
    nlinarith
  have oldRadiusPositive : 0 < radiusScale * distanceRate⁻¹ ^ level :=
    mul_pos radiusScalePositive (pow_pos (inv_pos.mpr distanceRatePositive) level)
  have oldMassPositive : 0 < law.real (closedBall point (radiusScale * distanceRate⁻¹ ^ level)) :=
    ENNReal.toReal_pos (Metric.measure_closedBall_pos law point oldRadiusPositive).ne'
      (measure_ne_top law _)
  have massComparison : law.real (closedBall point (radiusScale * distanceRate⁻¹ ^ level)) ≤
      law.real (ball point ((2 * radiusCoefficient) * (time.val : ℝ) ^ exponent)) :=
    measureReal_mono (closedBall_subset_ball radiusStrict)
  exact (div_le_div_of_nonneg_left coefficientPositive.le oldMassPositive massComparison).trans
    (levelLower level time timeAtLevel point)

end
end IGS.Sec31

#print axioms IGS.Sec31.inverse_open_ball_lower_of_geometric_closed_balls
