import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic

/-! Exact power-law optimization of a geometric two-scale Nash inequality.
The logarithmic exponent depends on mass growth and the product time scale;
there is no assumption that a separate resistance factor exceeds one. -/

namespace IGS.Sec31

theorem geometric_two_scale_choice
    (timeRate massRate exponent energyConstant tolerance : ℝ)
    (timeRateGreaterThanOne : 1 < timeRate)
    (exponentNonnegative : 0 ≤ exponent)
    (growthIdentity : massRate = timeRate ^ exponent)
    (energyPositive : 0 < energyConstant) (tolerancePositive : 0 < tolerance)
    (toleranceAtMost : tolerance ≤ energyConstant) :
    ∃ level : ℕ, energyConstant / timeRate ^ level ≤ tolerance ∧
      massRate ^ level ≤ (timeRate * energyConstant / tolerance) ^ exponent := by
  have timeRatePositive : 0 < timeRate := zero_lt_one.trans timeRateGreaterThanOne
  obtain ⟨level, lower, upper⟩ := exists_nat_pow_near
    ((le_div_iff₀ tolerancePositive).mpr (by simpa only [one_mul] using toleranceAtMost))
    timeRateGreaterThanOne
  refine ⟨level + 1, ?_, ?_⟩
  · apply (div_le_iff₀ (pow_pos timeRatePositive _)).mpr
    have strict := (div_lt_iff₀ tolerancePositive).mp upper
    nlinarith
  · have scaleUpper : timeRate ^ (level + 1) ≤ timeRate * energyConstant / tolerance := by
      rw [pow_succ, mul_comm (timeRate ^ level), mul_div_assoc]
      exact mul_le_mul_of_nonneg_left lower timeRatePositive.le
    calc
      massRate ^ (level + 1) = (timeRate ^ (level + 1)) ^ exponent := by
        rw [growthIdentity, ← Real.rpow_mul_natCast timeRatePositive.le,
          mul_comm exponent, Real.rpow_natCast_mul timeRatePositive.le]
      _ ≤ (timeRate * energyConstant / tolerance) ^ exponent :=
        Real.rpow_le_rpow (pow_nonneg timeRatePositive.le _) scaleUpper exponentNonnegative

theorem geometric_two_scale_epsilon_bound
    (timeRate massRate exponent energyConstant l1Constant energy l1Squared squareNorm tolerance : ℝ)
    (timeRateGreaterThanOne : 1 < timeRate) (exponentNonnegative : 0 ≤ exponent)
    (growthIdentity : massRate = timeRate ^ exponent)
    (energyPositive : 0 < energyConstant) (l1Nonnegative : 0 ≤ l1Constant)
    (energyNonnegative : 0 ≤ energy) (squareNonnegative : 0 ≤ l1Squared)
    (twoScale : ∀ level : ℕ, squareNorm ≤ energyConstant / timeRate ^ level * energy +
      l1Constant * massRate ^ level * l1Squared)
    (tolerancePositive : 0 < tolerance) (toleranceAtMost : tolerance ≤ energyConstant) :
    squareNorm ≤ tolerance * energy +
      l1Constant * (timeRate * energyConstant / tolerance) ^ exponent * l1Squared := by
  obtain ⟨level, energyBound, growthBound⟩ := geometric_two_scale_choice timeRate massRate exponent
    energyConstant tolerance timeRateGreaterThanOne exponentNonnegative growthIdentity energyPositive
    tolerancePositive toleranceAtMost
  exact (twoScale level).trans (add_le_add
    (mul_le_mul_of_nonneg_right energyBound energyNonnegative)
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left growthBound l1Nonnegative) squareNonnegative))

theorem geometric_growth_logarithmic_exponent
    (timeRate massRate : ℝ) (timeRateGreaterThanOne : 1 < timeRate)
    (massRateAtLeastOne : 1 ≤ massRate) :
    0 ≤ Real.log massRate / Real.log timeRate ∧
      massRate = timeRate ^ (Real.log massRate / Real.log timeRate) := by
  have timeRatePositive : 0 < timeRate := zero_lt_one.trans timeRateGreaterThanOne
  have logTimePositive : 0 < Real.log timeRate := Real.log_pos timeRateGreaterThanOne
  refine ⟨div_nonneg (Real.log_nonneg massRateAtLeastOne) logTimePositive.le, ?_⟩
  rw [Real.rpow_def_of_pos timeRatePositive]
  have cancellation : Real.log timeRate * (Real.log massRate / Real.log timeRate) = Real.log massRate := by
    field_simp [ne_of_gt logTimePositive]
  rw [cancellation, Real.exp_log (zero_lt_one.trans_le massRateAtLeastOne)]

end IGS.Sec31

#print axioms IGS.Sec31.geometric_two_scale_choice
#print axioms IGS.Sec31.geometric_two_scale_epsilon_bound
#print axioms IGS.Sec31.geometric_growth_logarithmic_exponent
