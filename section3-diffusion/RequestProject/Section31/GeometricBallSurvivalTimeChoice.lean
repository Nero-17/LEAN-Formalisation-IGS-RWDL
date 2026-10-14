import RequestProject.Section31.NashTwoScaleOptimization

/-! Choose a geometric spatial scale inside every sufficiently small ball,
with its native time scale bounded below by the continuous walk power.
Candidate scalar source; it has no probabilistic conclusion as an input. -/

namespace IGS.Sec31
noncomputable section

theorem geometric_ball_survival_time_choice
    (distanceRate timeRate radiusScale timeScale : ℝ)
    (distanceGreaterThanOne : 1 < distanceRate) (timeGreaterThanOne : 1 < timeRate)
    (radiusScalePositive : 0 < radiusScale) (timeScalePositive : 0 < timeScale) :
    ∃ timeConstant : ℝ, 0 < timeConstant ∧
      ∀ radius : ℝ, 0 < radius → radius ≤ radiusScale →
      ∃ level : ℕ, radiusScale * distanceRate⁻¹ ^ level ≤ radius ∧
        timeConstant * radius ^ (Real.log timeRate / Real.log distanceRate) ≤
          timeScale * timeRate⁻¹ ^ level := by
  have distancePositive := zero_lt_one.trans distanceGreaterThanOne
  have timePositive := zero_lt_one.trans timeGreaterThanOne
  let exponent := Real.log timeRate / Real.log distanceRate
  obtain ⟨exponentNonnegative, growthIdentity⟩ := geometric_growth_logarithmic_exponent
    distanceRate timeRate distanceGreaterThanOne timeGreaterThanOne.le
  let timeConstant := timeScale / (distanceRate * radiusScale) ^ exponent
  have timeConstantPositive : 0 < timeConstant := div_pos timeScalePositive
    (Real.rpow_pos_of_pos (mul_pos distancePositive radiusScalePositive) exponent)
  refine ⟨timeConstant, timeConstantPositive, ?_⟩
  intro radius radiusPositive radiusSmall
  obtain ⟨level, radiusBound, timeGrowth⟩ := geometric_two_scale_choice
    distanceRate timeRate exponent radiusScale radius distanceGreaterThanOne
    exponentNonnegative growthIdentity radiusScalePositive radiusPositive radiusSmall
  refine ⟨level, by simpa only [inv_pow, div_eq_mul_inv] using radiusBound, ?_⟩
  rw [inv_pow, ← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos timePositive level)).mpr
  have bound : timeRate ^ level * (timeConstant * radius ^ exponent) ≤
      (distanceRate * radiusScale / radius) ^ exponent * (timeConstant * radius ^ exponent) :=
    mul_le_mul_of_nonneg_right timeGrowth
      (mul_nonneg timeConstantPositive.le (Real.rpow_nonneg radiusPositive.le _))
  have cancellation : (distanceRate * radiusScale / radius) ^ exponent *
      (timeConstant * radius ^ exponent) = timeScale := by
    dsimp only [timeConstant]
    rw [Real.div_rpow (mul_nonneg distancePositive.le radiusScalePositive.le) radiusPositive.le]
    field_simp [(Real.rpow_pos_of_pos radiusPositive exponent).ne',
      (Real.rpow_pos_of_pos (mul_pos distancePositive radiusScalePositive) exponent).ne']
    <;> ring
  exact (by simpa only [mul_comm] using bound.trans_eq cancellation)

end
end IGS.Sec31

#print axioms IGS.Sec31.geometric_ball_survival_time_choice
