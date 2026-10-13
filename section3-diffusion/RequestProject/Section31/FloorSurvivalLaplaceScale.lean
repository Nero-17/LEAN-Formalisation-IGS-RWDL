import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Floor.Ring

/-! An exact floor-clock bridge. Surviving through floor(jumpRate*timeScale)
means the integer exit duration is strictly greater than that floor. This
implies the real scaled duration exceeds one, even when the floor is zero.
No lower bound on the number of sampled steps is needed. -/

namespace IGS.Sec31

noncomputable section

theorem exp_neg_duration_div_le_of_floor_lt {jumpRate timeScale : ℝ}
    (jumpPositive : 0 < jumpRate) (timePositive : 0 < timeScale) (duration : ℕ)
    (survives : ⌊jumpRate * timeScale⌋₊ < duration) :
    Real.exp (-(duration : ℝ) / (jumpRate * timeScale)) ≤ Real.exp (-1) := by
  have durationLarge : jumpRate * timeScale < (duration : ℝ) := Nat.lt_of_floor_lt survives
  apply Real.exp_le_exp.mpr
  have ratioLarge : 1 ≤ (duration : ℝ) / (jumpRate * timeScale) :=
    (le_div_iff₀ (mul_pos jumpPositive timePositive)).mpr (by simpa using durationLarge.le)
  rw [neg_div]
  linarith

/-- The pointwise bound whose expectation yields the usual Laplace
contraction from a survival probability. -/
theorem exp_neg_duration_div_le_survival_discount {jumpRate timeScale : ℝ}
    (jumpPositive : 0 < jumpRate) (timePositive : 0 < timeScale) (duration : ℕ) :
    Real.exp (-(duration : ℝ) / (jumpRate * timeScale)) ≤
      1 - (1 - Real.exp (-1)) * (if ⌊jumpRate * timeScale⌋₊ < duration then (1 : ℝ) else 0) := by
  by_cases survives : ⌊jumpRate * timeScale⌋₊ < duration
  · simpa only [if_pos survives, mul_one, sub_sub_cancel] using
      exp_neg_duration_div_le_of_floor_lt jumpPositive timePositive duration survives
  · simp only [if_neg survives, mul_zero, sub_zero]
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg duration))
      (mul_pos jumpPositive timePositive).le

end
end IGS.Sec31

#print axioms IGS.Sec31.exp_neg_duration_div_le_of_floor_lt
#print axioms IGS.Sec31.exp_neg_duration_div_le_survival_discount
