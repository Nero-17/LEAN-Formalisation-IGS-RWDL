import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

/-! The manuscript's degree-dimension-infinity logarithmic lower clause
follows from the stronger all-point pure-power bound. No real division by
logarithm of degree rate1 is used. -/
namespace IGS.Sec31
open scoped NNReal
noncomputable section

theorem logarithmic_lower_of_diagonal_power_lower
    {Space : Type*}
    (diagonal : {time : ℝ≥0 // 0 < time} → Space → ℝ)
    (exponent coefficient cutoffTime : ℝ)
    (coefficientPositive : 0 < coefficient) (cutoffPositive : 0 < cutoffTime)
    (powerLower : ∀ time : {time : ℝ≥0 // 0 < time}, (time.val : ℝ) ≤ cutoffTime →
      ∀ point : Space, coefficient / (time.val : ℝ) ^ exponent ≤ diagonal time point) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ logarithmicCutoff : ℝ, 0 < logarithmicCutoff ∧
      ∀ time : {time : ℝ≥0 // 0 < time}, (time.val : ℝ) ≤ logarithmicCutoff → ∀ point : Space,
        coefficient * (time.val : ℝ) ^ (-exponent) *
          |Real.log (time.val : ℝ)| ^ (-epsilon) ≤ diagonal time point := by
  intro epsilon epsilonPositive
  refine ⟨min cutoffTime (Real.exp (-1)), lt_min cutoffPositive (Real.exp_pos _), ?_⟩
  intro time timeSmall point
  have timePositive : 0 < (time.val : ℝ) := time.property
  have logarithmSmall : Real.log (time.val : ℝ) ≤ -1 := by
    have comparison := Real.log_le_log timePositive (timeSmall.trans (min_le_right _ _))
    simpa only [Real.log_exp] using comparison
  have logarithmMagnitude : 1 ≤ |Real.log (time.val : ℝ)| := by
    rw [abs_of_nonpos (by linarith : Real.log (time.val : ℝ) ≤ 0)]
    linarith
  have correctionAtMostOne := Real.rpow_le_one_of_one_le_of_nonpos logarithmMagnitude
    (neg_nonpos.mpr epsilonPositive.le)
  have pureNonnegative : 0 ≤ coefficient * (time.val : ℝ) ^ (-exponent) :=
    mul_nonneg coefficientPositive.le (Real.rpow_nonneg timePositive.le _)
  calc
    coefficient * (time.val : ℝ) ^ (-exponent) * |Real.log (time.val : ℝ)| ^ (-epsilon) ≤
        coefficient * (time.val : ℝ) ^ (-exponent) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left correctionAtMostOne pureNonnegative
    _ ≤ diagonal time point := by
      simpa only [Real.rpow_neg timePositive.le, div_eq_mul_inv] using
        powerLower time (timeSmall.trans (min_le_left _ _)) point

end
end IGS.Sec31

#print axioms IGS.Sec31.logarithmic_lower_of_diagonal_power_lower
