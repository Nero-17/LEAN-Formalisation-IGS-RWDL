import RequestProject.Section31.GeometricBackwardIteration
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Dyadic time scaling of the precise Nash recurrence. The boundedness and
recurrence are explicit generic inputs; the actual closed semigroup supplies
them through contraction and its proved half-time energy estimate. -/

namespace IGS.Sec31

open scoped NNReal

theorem dyadic_half_time_nash_bound
    (values : ℝ≥0 → ℝ) (timeRate energyConstant l1Constant exponent theta l1Squared bound : ℝ)
    (timeRatePositive : 0 < timeRate) (energyPositive : 0 < energyConstant)
    (l1Nonnegative : 0 ≤ l1Constant) (exponentNonnegative : 0 ≤ exponent)
    (thetaPositive : 0 < theta) (thetaLessThanOne : theta < 1)
    (productLessThanOne : theta * (2 : ℝ) ^ exponent < 1) (squareNonnegative : 0 ≤ l1Squared)
    (bounded : ∀ time, values time ≤ bound)
    (recurrence : ∀ (time : ℝ≥0), 0 < time → theta * (time : ℝ) ≤ energyConstant →
      values time ≤ theta * values (time / 2) +
        l1Constant * (timeRate * energyConstant / (theta * (time : ℝ))) ^ exponent * l1Squared)
    (time : ℝ≥0) (timePositive : 0 < time)
    (toleranceAtMost : theta * (time : ℝ) ≤ energyConstant) :
    values time ≤
      (l1Constant * (timeRate * energyConstant / (theta * (time : ℝ))) ^ exponent * l1Squared) /
        (1 - theta * (2 : ℝ) ^ exponent) := by
  have timeRealPositive : 0 < (time : ℝ) := timePositive
  have scaledBasePositive : 0 < timeRate * energyConstant / (theta * (time : ℝ)) := by positivity
  have scaledRecurrence (index : ℕ) :
      values (time / 2 ^ index) ≤ theta * values (time / 2 ^ (index + 1)) +
        (l1Constant * (timeRate * energyConstant / (theta * (time : ℝ))) ^ exponent * l1Squared) *
          ((2 : ℝ) ^ exponent) ^ index := by
    have scaledTimePositive : 0 < time / 2 ^ index := by positivity
    have scaledTimeAtMost : theta * ((time / 2 ^ index : ℝ≥0) : ℝ) ≤ energyConstant := by
      apply le_trans (mul_le_mul_of_nonneg_left ?_ thetaPositive.le) toleranceAtMost
      simp only [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat]
      exact div_le_self time.coe_nonneg (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    have estimate := recurrence (time / 2 ^ index) scaledTimePositive scaledTimeAtMost
    have halfIdentity : (time / 2 ^ index) / 2 = time / 2 ^ (index + 1) := by
      rw [div_div, pow_succ]
    have coefficientIdentity :
        timeRate * energyConstant / (theta * ((time / 2 ^ index : ℝ≥0) : ℝ)) =
          (timeRate * energyConstant / (theta * (time : ℝ))) * (2 : ℝ) ^ index := by
      simp only [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat]
      field_simp [ne_of_gt thetaPositive, ne_of_gt timeRealPositive]
    have powerIdentity : ((2 : ℝ) ^ index) ^ exponent = ((2 : ℝ) ^ exponent) ^ index := by
      rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm (index : ℝ),
        Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    rw [halfIdentity, coefficientIdentity,
      Real.mul_rpow scaledBasePositive.le (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) index), powerIdentity] at estimate
    convert estimate using 1 <;> ring
  have iteration := geometric_backward_iteration_bound (fun index => values (time / 2 ^ index))
    theta ((2 : ℝ) ^ exponent)
    (l1Constant * (timeRate * energyConstant / (theta * (time : ℝ))) ^ exponent * l1Squared) bound
    thetaPositive.le thetaLessThanOne (Real.rpow_nonneg (by norm_num) _)
    (by positivity) productLessThanOne (fun index => bounded _) scaledRecurrence
  simpa only [pow_zero, div_one] using iteration

theorem nash_dyadic_theta (exponent : ℝ) (exponentNonnegative : 0 ≤ exponent) :
    0 < (2 * (2 : ℝ) ^ exponent)⁻¹ ∧
      (2 * (2 : ℝ) ^ exponent)⁻¹ < 1 ∧
      (2 * (2 : ℝ) ^ exponent)⁻¹ * (2 : ℝ) ^ exponent = 1 / 2 := by
  have growthPositive : 0 < (2 : ℝ) ^ exponent := Real.rpow_pos_of_pos (by norm_num) _
  have growthAtLeastOne : 1 ≤ (2 : ℝ) ^ exponent := Real.one_le_rpow (by norm_num) exponentNonnegative
  refine ⟨by positivity, ?_, ?_⟩
  · apply (inv_lt_one₀ (by positivity : 0 < 2 * (2 : ℝ) ^ exponent)).mpr
    nlinarith
  · field_simp [ne_of_gt growthPositive]

end IGS.Sec31

#print axioms IGS.Sec31.dyadic_half_time_nash_bound
#print axioms IGS.Sec31.nash_dyadic_theta
