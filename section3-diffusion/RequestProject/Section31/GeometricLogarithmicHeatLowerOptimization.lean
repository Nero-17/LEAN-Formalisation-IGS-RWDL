import RequestProject.Section31.GeometricLogarithmicHeatTimeChoice
import RequestProject.Section31.GeometricLogarithmicHeatLower

/-! Full scalar optimization of eventual geometric-level lower estimates.
The eventual level threshold enters only the positive small-time cutoff.
This helper's level estimate must be filled by the actual kernel consumer;
it supplies neither a model volume estimate nor a model survival estimate.
Candidate source: no compilation is claimed. -/

namespace IGS.Sec31
noncomputable section

theorem geometric_logarithmic_heat_lower_of_eventual_levels
    (timeRate massRate exponent logExponent timeScale coefficient : ℝ)
    (timeRateGreaterThanOne : 1 < timeRate) (exponentNonnegative : 0 ≤ exponent)
    (growthIdentity : massRate = timeRate ^ exponent) (logExponentNonnegative : 0 ≤ logExponent)
    (timeScalePositive : 0 < timeScale) (coefficientPositive : 0 < coefficient)
    (threshold : ℕ) (diagonal : ℝ → ℝ)
    (levelLower : ∀ level : ℕ, threshold ≤ level → ∀ time : ℝ, 0 < time →
      time ≤ timeScale / timeRate ^ level →
      coefficient * massRate ^ level / (level + 2 : ℝ) ^ logExponent ≤ diagonal time) :
    ∃ lowerConstant : ℝ, 0 < lowerConstant ∧ ∃ timeThreshold : ℝ, 0 < timeThreshold ∧
      ∀ time : ℝ, 0 < time → time ≤ timeThreshold →
      lowerConstant * time ^ (-exponent) * |Real.log time| ^ (-logExponent) ≤ diagonal time := by
  have timeRatePositive := zero_lt_one.trans timeRateGreaterThanOne
  have logRatePositive := Real.log_pos timeRateGreaterThanOne
  let logConstant := (|Real.log timeScale| + 1 + 2 * Real.log timeRate) / Real.log timeRate
  have logConstantPositive : 0 < logConstant := by
    dsimp only [logConstant]
    exact div_pos (by positivity) logRatePositive
  let lowerConstant := coefficient * (timeScale / timeRate) ^ exponent / logConstant ^ logExponent
  have lowerConstantPositive : 0 < lowerConstant := by
    dsimp only [lowerConstant]
    exact div_pos
      (mul_pos coefficientPositive (Real.rpow_pos_of_pos (div_pos timeScalePositive timeRatePositive) _))
      (Real.rpow_pos_of_pos logConstantPositive _)
  refine ⟨lowerConstant, lowerConstantPositive,
    min (timeScale / timeRate ^ threshold) (Real.exp (-1)),
    lt_min (div_pos timeScalePositive (pow_pos timeRatePositive _)) (Real.exp_pos _), ?_⟩
  intro time timePositive timeSmall
  obtain ⟨level, afterThreshold, lower, upper, logarithmBound⟩ := geometric_heat_time_level_with_log_bound
    timeRate timeScale time timeRateGreaterThanOne timeScalePositive timePositive threshold
    (timeSmall.trans (min_le_left _ _)) (timeSmall.trans (min_le_right _ _))
  have atLevel : time ≤ timeScale / timeRate ^ level :=
    (le_div_iff₀ (pow_pos timeRatePositive level)).mpr (by
      simpa only [mul_comm] using (le_div_iff₀ timePositive).mp lower)
  have absoluteLogPositive : 0 < |Real.log time| := by
    have levelPositive : 0 < (level + 2 : ℝ) := by positivity
    change (level + 2 : ℝ) ≤ logConstant * |Real.log time| at logarithmBound
    nlinarith
  exact geometric_logarithmic_heat_lower_at_level timeRate massRate exponent logExponent timeScale logConstant
    coefficient time (diagonal time) timeRatePositive exponentNonnegative growthIdentity logExponentNonnegative
    timeScalePositive logConstantPositive coefficientPositive.le timePositive absoluteLogPositive level upper
    logarithmBound (levelLower level afterThreshold time timePositive atLevel)

end
end IGS.Sec31

#print axioms IGS.Sec31.geometric_logarithmic_heat_lower_of_eventual_levels
