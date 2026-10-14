import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Scalar consumption of a geometric-level diagonal lower estimate.
The chosen level's time and logarithmic bounds give exactly the polynomial
heat exponent and the same logarithmic exponent, with a fixed constant.
The geometric lower estimate is an intermediate scalar input to be filled
by the actual same-semigroup cutoff and ball-volume consumer.
Candidate source: no compilation is claimed. -/

namespace IGS.Sec31
noncomputable section

theorem geometric_logarithmic_heat_lower_at_level
    (timeRate massRate exponent logExponent timeScale logConstant coefficient time diagonal : ℝ)
    (timeRatePositive : 0 < timeRate) (exponentNonnegative : 0 ≤ exponent)
    (growthIdentity : massRate = timeRate ^ exponent) (logExponentNonnegative : 0 ≤ logExponent)
    (timeScalePositive : 0 < timeScale) (logConstantPositive : 0 < logConstant)
    (coefficientNonnegative : 0 ≤ coefficient) (timePositive : 0 < time)
    (absoluteLogPositive : 0 < |Real.log time|) (level : ℕ)
    (levelTime : timeScale / time < timeRate ^ (level + 1))
    (levelLog : (level + 2 : ℝ) ≤ logConstant * |Real.log time|)
    (levelLower : coefficient * massRate ^ level / (level + 2 : ℝ) ^ logExponent ≤ diagonal) :
    (coefficient * (timeScale / timeRate) ^ exponent / logConstant ^ logExponent) *
      time ^ (-exponent) * |Real.log time| ^ (-logExponent) ≤ diagonal := by
  have massPositive : 0 < massRate := by
    rw [growthIdentity]
    exact Real.rpow_pos_of_pos timeRatePositive _
  have basePositive : 0 < timeScale / (timeRate * time) := by positivity
  have timePowerLower : timeScale / (timeRate * time) ≤ timeRate ^ level := by
    have divided : (timeScale / time) / timeRate < timeRate ^ level :=
      (div_lt_iff₀ timeRatePositive).mpr (by simpa only [pow_succ] using levelTime)
    simpa only [div_div, mul_comm time timeRate] using divided.le
  have massLower : (timeScale / (timeRate * time)) ^ exponent ≤ massRate ^ level := by
    calc
      _ ≤ (timeRate ^ level) ^ exponent :=
        Real.rpow_le_rpow basePositive.le timePowerLower exponentNonnegative
      _ = massRate ^ level := by
        rw [growthIdentity, ← Real.rpow_mul_natCast timeRatePositive.le,
          mul_comm exponent, Real.rpow_natCast_mul timeRatePositive.le]
  have logarithmCost : (level + 2 : ℝ) ^ logExponent ≤
      (logConstant * |Real.log time|) ^ logExponent :=
    Real.rpow_le_rpow (by positivity) levelLog logExponentNonnegative
  have compared : coefficient * (timeScale / (timeRate * time)) ^ exponent /
      (logConstant * |Real.log time|) ^ logExponent ≤
      coefficient * massRate ^ level / (level + 2 : ℝ) ^ logExponent :=
    div_le_div₀ (mul_nonneg coefficientNonnegative (pow_nonneg massPositive.le level))
      (mul_le_mul_of_nonneg_left massLower coefficientNonnegative)
      (Real.rpow_pos_of_pos (by positivity) _) logarithmCost
  have profileIdentity :
      (coefficient * (timeScale / timeRate) ^ exponent / logConstant ^ logExponent) *
        time ^ (-exponent) * |Real.log time| ^ (-logExponent) =
      coefficient * (timeScale / (timeRate * time)) ^ exponent /
        (logConstant * |Real.log time|) ^ logExponent := by
    have dividedBase : timeScale / (timeRate * time) = (timeScale / timeRate) / time :=
      (div_div timeScale timeRate time).symm
    rw [dividedBase,
      Real.div_rpow (div_pos timeScalePositive timeRatePositive).le timePositive.le,
      Real.mul_rpow logConstantPositive.le absoluteLogPositive.le,
      Real.rpow_neg timePositive.le, Real.rpow_neg absoluteLogPositive.le]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [profileIdentity]
  exact compared.trans levelLower

end
end IGS.Sec31

#print axioms IGS.Sec31.geometric_logarithmic_heat_lower_at_level
