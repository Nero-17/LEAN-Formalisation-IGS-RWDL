import RequestProject.Section31.NashTwoScaleOptimization

/-! Optimize the actual degree-corrected diagonal recurrence. The geometric
growth is mass/degree and its product with degree*resistance is the actual
time scale. No separate resistance-greater-than-one assumption is used. -/

namespace IGS.Sec31

theorem diagonal_le_of_square_le_multiple (diagonal coefficient : ℝ)
    (diagonalNonnegative : 0 ≤ diagonal)
    (coefficientNonnegative : 0 ≤ coefficient)
    (squareBound : diagonal ^ 2 ≤ coefficient * diagonal) :
    diagonal ≤ coefficient := by
  by_cases diagonalZero : diagonal = 0
  · simpa [diagonalZero] using coefficientNonnegative
  · have diagonalPositive : 0 < diagonal := lt_of_le_of_ne diagonalNonnegative (Ne.symm diagonalZero)
    by_contra notBound
    have productPositive := mul_pos (sub_pos.mpr (lt_of_not_ge notBound)) diagonalPositive
    nlinarith

theorem geometric_diagonal_heat_upper
    (timeRate growthRate decayRate exponent normConstant energyConstant time diagonal : ℝ)
    (timeRateGreaterThanOne : 1 < timeRate)
    (growthPositive : 0 < growthRate) (decayPositive : 0 < decayRate)
    (timeScaleIdentity : timeRate = growthRate * decayRate)
    (exponentNonnegative : 0 ≤ exponent)
    (growthIdentity : growthRate = timeRate ^ exponent)
    (normNonnegative : 0 ≤ normConstant) (energyNonnegative : 0 ≤ energyConstant)
    (timePositive : 0 < time) (timeAtMostOne : time ≤ 1)
    (diagonalNonnegative : 0 ≤ diagonal)
    (pointRecurrence : ∀ level : ℕ,
      diagonal ^ 2 ≤ (normConstant * growthRate ^ level +
        energyConstant / (decayRate ^ level * time)) * diagonal) :
    diagonal ≤ (normConstant + energyConstant) * (timeRate / time) ^ exponent := by
  obtain ⟨level, timeBound, growthBound⟩ := geometric_two_scale_choice
    timeRate growthRate exponent 1 time timeRateGreaterThanOne exponentNonnegative
    growthIdentity (by norm_num) timePositive timeAtMostOne
  have denominatorPositive : 0 < decayRate ^ level * time :=
    mul_pos (pow_pos decayPositive level) timePositive
  have scaleBound : 1 ≤ time * timeRate ^ level :=
    (div_le_iff₀ (pow_pos (zero_lt_one.trans timeRateGreaterThanOne) level)).mp timeBound
  have inverseBound : 1 / (decayRate ^ level * time) ≤ growthRate ^ level := by
    apply (div_le_iff₀ denominatorPositive).mpr
    calc
      1 ≤ time * timeRate ^ level := scaleBound
      _ = growthRate ^ level * (decayRate ^ level * time) := by
        rw [timeScaleIdentity, mul_pow]
        ring
  have coefficientBound : normConstant * growthRate ^ level +
      energyConstant / (decayRate ^ level * time) ≤
        (normConstant + energyConstant) * growthRate ^ level := by
    have energyBound := mul_le_mul_of_nonneg_left inverseBound energyNonnegative
    simp only [mul_one_div] at energyBound
    nlinarith
  have pointBound := diagonal_le_of_square_le_multiple diagonal
    (normConstant * growthRate ^ level + energyConstant / (decayRate ^ level * time))
    diagonalNonnegative (by positivity) (pointRecurrence level)
  simpa only [mul_one] using (pointBound.trans coefficientBound).trans
    (mul_le_mul_of_nonneg_left growthBound (add_nonneg normNonnegative energyNonnegative))

theorem geometric_diagonal_heat_upper_power_law
    (timeRate growthRate decayRate normConstant energyConstant time diagonal : ℝ)
    (timeRateGreaterThanOne : 1 < timeRate)
    (growthAtLeastOne : 1 ≤ growthRate) (decayPositive : 0 < decayRate)
    (timeScaleIdentity : timeRate = growthRate * decayRate)
    (normNonnegative : 0 ≤ normConstant) (energyNonnegative : 0 ≤ energyConstant)
    (timePositive : 0 < time) (timeAtMostOne : time ≤ 1)
    (diagonalNonnegative : 0 ≤ diagonal)
    (pointRecurrence : ∀ level : ℕ,
      diagonal ^ 2 ≤ (normConstant * growthRate ^ level +
        energyConstant / (decayRate ^ level * time)) * diagonal) :
    diagonal ≤ ((normConstant + energyConstant) * growthRate) /
      time ^ (Real.log growthRate / Real.log timeRate) := by
  obtain ⟨exponentNonnegative, growthIdentity⟩ := geometric_growth_logarithmic_exponent
    timeRate growthRate timeRateGreaterThanOne growthAtLeastOne
  have bound := geometric_diagonal_heat_upper timeRate growthRate decayRate
    (Real.log growthRate / Real.log timeRate) normConstant energyConstant time diagonal
    timeRateGreaterThanOne (zero_lt_one.trans_le growthAtLeastOne) decayPositive
    timeScaleIdentity exponentNonnegative growthIdentity normNonnegative energyNonnegative
    timePositive timeAtMostOne diagonalNonnegative pointRecurrence
  rw [Real.div_rpow (zero_lt_one.trans timeRateGreaterThanOne).le timePositive.le,
    ← growthIdentity, ← mul_div_assoc] at bound
  exact bound

theorem degree_corrected_diagonal_heat_upper
    (massRate degreeRate resistanceRate normConstant energyConstant time diagonal : ℝ)
    (massPositive : 0 < massRate) (degreePositive : 0 < degreeRate)
    (resistancePositive : 0 < resistanceRate)
    (degreeAtMostMass : degreeRate ≤ massRate)
    (timeRateGreaterThanOne : 1 < massRate * resistanceRate)
    (normNonnegative : 0 ≤ normConstant) (energyNonnegative : 0 ≤ energyConstant)
    (birth : ℕ) (timePositive : 0 < time) (timeAtMostOne : time ≤ 1)
    (diagonalNonnegative : 0 ≤ diagonal)
    (pointRecurrence : ∀ level : ℕ,
      diagonal ^ 2 ≤ (normConstant * (massRate ^ (birth + level) / degreeRate ^ level) +
        energyConstant / (degreeRate ^ level * resistanceRate ^ (birth + level) * time)) * diagonal) :
    diagonal ≤ ((normConstant * massRate ^ birth + energyConstant / resistanceRate ^ birth) *
      (massRate / degreeRate)) /
        time ^ ((Real.log massRate - Real.log degreeRate) / Real.log (massRate * resistanceRate)) := by
  have growthAtLeastOne : 1 ≤ massRate / degreeRate :=
    (one_le_div degreePositive).mpr degreeAtMostMass
  have timeScaleIdentity : massRate * resistanceRate =
      (massRate / degreeRate) * (degreeRate * resistanceRate) := by
    field_simp [degreePositive.ne']
  have rewrittenRecurrence : ∀ level : ℕ,
      diagonal ^ 2 ≤ ((normConstant * massRate ^ birth) * (massRate / degreeRate) ^ level +
        (energyConstant / resistanceRate ^ birth) /
          ((degreeRate * resistanceRate) ^ level * time)) * diagonal := by
    intro level
    have coefficientIdentity : normConstant * (massRate ^ (birth + level) / degreeRate ^ level) +
        energyConstant / (degreeRate ^ level * resistanceRate ^ (birth + level) * time) =
          (normConstant * massRate ^ birth) * (massRate / degreeRate) ^ level +
          (energyConstant / resistanceRate ^ birth) / ((degreeRate * resistanceRate) ^ level * time) := by
      rw [pow_add, pow_add, div_pow, mul_pow]
      field_simp [degreePositive.ne', resistancePositive.ne', timePositive.ne']
      <;> ring
    rw [← coefficientIdentity]
    exact pointRecurrence level
  have bound := geometric_diagonal_heat_upper_power_law (massRate * resistanceRate)
    (massRate / degreeRate) (degreeRate * resistanceRate)
    (normConstant * massRate ^ birth) (energyConstant / resistanceRate ^ birth)
    time diagonal timeRateGreaterThanOne growthAtLeastOne (mul_pos degreePositive resistancePositive)
    timeScaleIdentity (by positivity) (by positivity) timePositive timeAtMostOne
    diagonalNonnegative rewrittenRecurrence
  rw [Real.log_div massPositive.ne' degreePositive.ne'] at bound
  exact bound

end IGS.Sec31

#print axioms IGS.Sec31.diagonal_le_of_square_le_multiple
#print axioms IGS.Sec31.geometric_diagonal_heat_upper
#print axioms IGS.Sec31.geometric_diagonal_heat_upper_power_law
#print axioms IGS.Sec31.degree_corrected_diagonal_heat_upper
