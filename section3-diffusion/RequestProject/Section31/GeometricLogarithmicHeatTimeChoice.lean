import RequestProject.Section31.LogarithmicCollarSchedule
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Geometric time-level selection above an arbitrary eventual threshold,
with the explicit logarithmic level cost. The collar width is chosen so its
degree exponent is exactly the paper's exponent plus the requested epsilon.
These are scalar helpers; neither a volume nor a stay conclusion is assumed.
Candidate source: no compilation is claimed. -/

namespace IGS.Sec31
open scoped Topology
noncomputable section

theorem geometric_heat_time_level_with_log_bound
    (timeRate timeScale time : ℝ) (timeRateGreaterThanOne : 1 < timeRate)
    (timeScalePositive : 0 < timeScale) (timePositive : 0 < time) (threshold : ℕ)
    (timeSmall : time ≤ timeScale / timeRate ^ threshold)
    (timeLogSmall : time ≤ Real.exp (-1)) :
    ∃ level : ℕ, threshold ≤ level ∧ timeRate ^ level ≤ timeScale / time ∧
      timeScale / time < timeRate ^ (level + 1) ∧
      (level + 2 : ℝ) ≤
        ((|Real.log timeScale| + 1 + 2 * Real.log timeRate) / Real.log timeRate) * |Real.log time| := by
  have timeRatePositive := zero_lt_one.trans timeRateGreaterThanOne
  have logRatePositive := Real.log_pos timeRateGreaterThanOne
  have thresholdPower : timeRate ^ threshold ≤ timeScale / time :=
    (le_div_iff₀ timePositive).mpr (by
      have multiplied := (le_div_iff₀ (pow_pos timeRatePositive threshold)).mp timeSmall
      simpa only [mul_comm] using multiplied)
  have ratioAtLeastOne : 1 ≤ timeScale / time :=
    (one_le_pow₀ timeRateGreaterThanOne.le).trans thresholdPower
  obtain ⟨level, lower, upper⟩ := exists_nat_pow_near ratioAtLeastOne timeRateGreaterThanOne
  have thresholdAtMost : threshold ≤ level := by
    by_contra notOrdered
    have levelBefore : level + 1 ≤ threshold := Nat.succ_le_of_lt (Nat.lt_of_not_ge notOrdered)
    have powerBefore := pow_le_pow_right₀ timeRateGreaterThanOne.le levelBefore
    exact (not_lt_of_ge (powerBefore.trans thresholdPower)) upper
  refine ⟨level, thresholdAtMost, lower, upper, ?_⟩
  have logarithmBound := Real.log_le_log (pow_pos timeRatePositive level) lower
  rw [Real.log_pow, Real.log_div timeScalePositive.ne' timePositive.ne'] at logarithmBound
  have logTimeBound : Real.log time ≤ -1 := by
    have compared := Real.log_le_log timePositive timeLogSmall
    simpa only [Real.log_exp] using compared
  have absoluteLog : |Real.log time| = -Real.log time :=
    abs_of_nonpos (logTimeBound.trans (by norm_num))
  have logarithmLarge : 1 ≤ |Real.log time| := by rw [absoluteLog]; linarith
  have lossNonnegative : 0 ≤
      (|Real.log timeScale| + 2 * Real.log timeRate) * (|Real.log time| - 1) :=
    mul_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg (by norm_num) logRatePositive.le))
      (sub_nonneg.mpr logarithmLarge)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ logRatePositive).mpr
  rw [absoluteLog] at lossNonnegative ⊢
  nlinarith [le_abs_self (Real.log timeScale)]

theorem logarithmic_collar_width_for_exact_exponent (massRate degreeRate epsilon : ℝ)
    (degreeGreaterThanOne : 1 < degreeRate) (degreeMass : degreeRate < massRate)
    (epsilonPositive : 0 < epsilon) :
    ∃ width : ℝ, 1 / Real.log (massRate / degreeRate) < width ∧
      width * Real.log degreeRate =
        1 / (Real.log massRate / Real.log degreeRate - 1) + epsilon := by
  have degreePositive := zero_lt_one.trans degreeGreaterThanOne
  have massPositive := degreePositive.trans degreeMass
  have degreeLogPositive := Real.log_pos degreeGreaterThanOne
  refine ⟨1 / Real.log (massRate / degreeRate) + epsilon / Real.log degreeRate, ?_, ?_⟩
  · exact lt_add_of_pos_right _ (div_pos epsilonPositive degreeLogPositive)
  · have identity : 1 / Real.log (massRate / degreeRate) * Real.log degreeRate =
        Real.log degreeRate / (Real.log massRate - Real.log degreeRate) := by
      rw [Real.log_div massPositive.ne' degreePositive.ne']
      ring
    rw [add_mul, identity, div_mul_cancel₀ _ degreeLogPositive.ne',
      EIGS.degree_logarithmic_collar_exponent massRate degreeRate degreeGreaterThanOne degreeMass]

end
end IGS.Sec31

#print axioms IGS.Sec31.geometric_heat_time_level_with_log_bound
#print axioms IGS.Sec31.logarithmic_collar_width_for_exact_exponent
