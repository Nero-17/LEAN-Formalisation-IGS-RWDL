import RequestProject.Section31.NashTwoScaleOptimization

/-! The optimized product exponent is exactly the paper's sub-Gaussian
power for the actual logarithmic walk exponent. -/

namespace IGS.Sec31
noncomputable section

theorem logarithmic_subGaussian_exponent_identity
    (distanceRate timeRate radius time : ℝ)
    (distanceGreaterThanOne : 1 < distanceRate)
    (timeGreaterThanDistance : distanceRate < timeRate)
    (radiusPositive : 0 < radius) (timePositive : 0 < time) :
    radius * (radius / time) ^ (Real.log distanceRate / Real.log (timeRate / distanceRate)) =
      (radius ^ (Real.log timeRate / Real.log distanceRate) / time) ^
        (1 / (Real.log timeRate / Real.log distanceRate - 1)) := by
  have distancePositive := zero_lt_one.trans distanceGreaterThanOne
  have timeRatePositive := distancePositive.trans timeGreaterThanDistance
  have logDistancePositive := Real.log_pos distanceGreaterThanOne
  have logQuotientPositive : 0 < Real.log (timeRate / distanceRate) :=
    Real.log_pos ((one_lt_div distancePositive).mpr timeGreaterThanDistance)
  have logarithmDifferencePositive : 0 < Real.log timeRate - Real.log distanceRate := by
    simpa only [Real.log_div timeRatePositive.ne' distancePositive.ne'] using logQuotientPositive
  have exponentEquality : 1 / (Real.log timeRate / Real.log distanceRate - 1) =
      Real.log distanceRate / Real.log (timeRate / distanceRate) := by
    rw [Real.log_div timeRatePositive.ne' distancePositive.ne']
    field_simp [logDistancePositive.ne', logarithmDifferencePositive.ne']
    <;> ring
  have productEquality : (Real.log timeRate / Real.log distanceRate) *
      (Real.log distanceRate / Real.log (timeRate / distanceRate)) =
        1 + Real.log distanceRate / Real.log (timeRate / distanceRate) := by
    rw [Real.log_div timeRatePositive.ne' distancePositive.ne']
    field_simp [logDistancePositive.ne', logarithmDifferencePositive.ne']
    <;> ring
  rw [exponentEquality, Real.div_rpow (Real.rpow_nonneg radiusPositive.le _) timePositive.le,
    ← Real.rpow_mul radiusPositive.le, productEquality, Real.rpow_add radiusPositive,
    Real.rpow_one, Real.div_rpow radiusPositive.le timePositive.le]
  ring

end
end IGS.Sec31

#print axioms IGS.Sec31.logarithmic_subGaussian_exponent_identity
