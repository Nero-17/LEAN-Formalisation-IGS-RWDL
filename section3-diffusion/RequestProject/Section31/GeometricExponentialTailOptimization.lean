import RequestProject.Section31.NashTwoScaleOptimization
import Mathlib.Algebra.Order.Archimedean.Basic

/-! Optimize the genuine coarse-scale exponential envelope. This is a
numerical scale-selection lemma, not a stochastic tail assumption. The
integer level is also bounded by a prescribed fine level whenever the
optimal scale lies above the fine mesh. -/

namespace IGS.Sec31
noncomputable section

theorem geometric_exponential_envelope_choice
    (distanceRate timeRate timeCoefficient spatialCoefficient radius time offset : ℝ)
    (distanceGreaterThanOne : 1 < distanceRate)
    (timeGreaterThanDistance : distanceRate < timeRate)
    (timeCoefficientPositive : 0 < timeCoefficient)
    (spatialCoefficientPositive : 0 < spatialCoefficient)
    (radiusPositive : 0 < radius) (timePositive : 0 < time)
    (timeSmall : time ≤ spatialCoefficient * radius / (2 * timeCoefficient)) :
    ∃ level : ℕ,
      (timeRate / distanceRate) ^ level ≤ spatialCoefficient * radius / (2 * timeCoefficient * time) ∧
      spatialCoefficient * radius / (2 * timeCoefficient * time) < (timeRate / distanceRate) ^ (level + 1) ∧
      (∀ fine : ℕ, spatialCoefficient * radius / (2 * timeCoefficient * time) <
          (timeRate / distanceRate) ^ (fine + 1) → level ≤ fine) ∧
      Real.exp (offset + timeCoefficient * time * timeRate ^ level -
          spatialCoefficient * radius * distanceRate ^ level) ≤
        Real.exp offset * Real.exp (-(spatialCoefficient / (2 * distanceRate)) * radius *
          (spatialCoefficient * radius / (2 * timeCoefficient * time)) ^
            (Real.log distanceRate / Real.log (timeRate / distanceRate))) := by
  have distancePositive := zero_lt_one.trans distanceGreaterThanOne
  have timeRatePositive := distancePositive.trans timeGreaterThanDistance
  have quotientGreaterThanOne : 1 < timeRate / distanceRate :=
    (one_lt_div distancePositive).mpr timeGreaterThanDistance
  have quotientPositive := zero_lt_one.trans quotientGreaterThanOne
  have ratioPositive : 0 < spatialCoefficient * radius / (2 * timeCoefficient * time) := by positivity
  have ratioAtLeastOne : 1 ≤ spatialCoefficient * radius / (2 * timeCoefficient * time) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * timeCoefficient * time)).mpr
    have multiplied := (le_div_iff₀ (by positivity : 0 < 2 * timeCoefficient)).mp timeSmall
    nlinarith
  obtain ⟨level, lower, upper⟩ := exists_nat_pow_near ratioAtLeastOne quotientGreaterThanOne
  refine ⟨level, lower, upper, ?_, ?_⟩
  · intro fine beforeFine
    by_contra notBefore
    have fineBefore : fine + 1 ≤ level := Nat.succ_le_of_lt (Nat.lt_of_not_ge notBefore)
    have powerBefore := pow_le_pow_right₀ quotientGreaterThanOne.le fineBefore
    exact (not_lt_of_ge (powerBefore.trans lower)) beforeFine
  · have balance : timeCoefficient * time * (timeRate / distanceRate) ^ level ≤
        spatialCoefficient * radius / 2 := by
      have multiplied := (le_div_iff₀ (by positivity : 0 < 2 * timeCoefficient * time)).mp lower
      nlinarith
    have powerFactor : timeRate ^ level = distanceRate ^ level * (timeRate / distanceRate) ^ level := by
      rw [div_pow]
      field_simp [pow_ne_zero level distancePositive.ne']
    have temporal : timeCoefficient * time * timeRate ^ level ≤
        (spatialCoefficient * radius / 2) * distanceRate ^ level := by
      have multiplied := mul_le_mul_of_nonneg_right balance (pow_nonneg distancePositive.le level)
      simpa only [powerFactor] using (show
        timeCoefficient * time * (distanceRate ^ level * (timeRate / distanceRate) ^ level) ≤
          spatialCoefficient * radius / 2 * distanceRate ^ level by nlinarith [multiplied])
    obtain ⟨exponentNonnegative, growthIdentity⟩ := geometric_growth_logarithmic_exponent
      (timeRate / distanceRate) distanceRate quotientGreaterThanOne distanceGreaterThanOne.le
    have powerIdentity : ((timeRate / distanceRate) ^ (level + 1)) ^
        (Real.log distanceRate / Real.log (timeRate / distanceRate)) = distanceRate ^ (level + 1) := by
      calc
        _ = ((timeRate / distanceRate) ^
            (Real.log distanceRate / Real.log (timeRate / distanceRate))) ^ (level + 1) := by
          rw [← Real.rpow_mul_natCast quotientPositive.le,
            mul_comm (Real.log distanceRate / Real.log (timeRate / distanceRate)),
            Real.rpow_natCast_mul quotientPositive.le]
        _ = _ := by rw [← growthIdentity]
    have powerBound := Real.rpow_le_rpow ratioPositive.le upper.le exponentNonnegative
    rw [powerIdentity, pow_succ] at powerBound
    have optimized : spatialCoefficient / (2 * distanceRate) * radius *
        (spatialCoefficient * radius / (2 * timeCoefficient * time)) ^
          (Real.log distanceRate / Real.log (timeRate / distanceRate)) ≤
        (spatialCoefficient * radius / 2) * distanceRate ^ level := by
      have multiplied := mul_le_mul_of_nonneg_left powerBound
        (show 0 ≤ spatialCoefficient * radius / (2 * distanceRate) by positivity)
      have cancellation : spatialCoefficient * radius / (2 * distanceRate) *
          (distanceRate ^ level * distanceRate) =
          (spatialCoefficient * radius / 2) * distanceRate ^ level := by
        field_simp [distancePositive.ne']
        <;> ring
      rw [cancellation] at multiplied
      convert multiplied using 1 <;> ring
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [temporal, optimized]

end
end IGS.Sec31

#print axioms IGS.Sec31.geometric_exponential_envelope_choice
