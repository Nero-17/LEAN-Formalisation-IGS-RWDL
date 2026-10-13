import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-! A uniform tail estimate for the geometric resolvent clock. The hypotheses
are numerical thresholds on the actual jump rate, to be filled by its proved
divergence. No limiting exponential approximation is assumed. -/

namespace IGS.Sec31

theorem geometric_resolvent_floor_clock_tail
    (step window rate : ℝ)
    (stepPositive : 0 < step) (windowPositive : 0 < window) (ratePositive : 0 < rate)
    (windowRateLarge : 2 ≤ window * rate) (stepRateLarge : 1 ≤ step * rate) :
    (step * rate / (1 + step * rate)) ^ ⌊window * rate⌋₊ ≤
      Real.exp (-window / (4 * step)) := by
  have denominatorPositive : 0 < 1 + step * rate := by positivity
  have ratioNonnegative : 0 ≤ step * rate / (1 + step * rate) := by positivity
  have ratioBound : step * rate / (1 + step * rate) ≤
      Real.exp (-(1 + step * rate)⁻¹) := by
    have comparison := Real.add_one_le_exp (-(1 + step * rate)⁻¹)
    have equality : step * rate / (1 + step * rate) = -(1 + step * rate)⁻¹ + 1 := by
      field_simp [ne_of_gt denominatorPositive]
      ring
    rw [equality]
    exact comparison
  have floorLower : window * rate / 2 ≤ (⌊window * rate⌋₊ : ℝ) := by
    have floorEstimate := Nat.lt_floor_add_one (window * rate)
    linarith
  have quotientLower : window / (4 * step) ≤
      (⌊window * rate⌋₊ : ℝ) / (1 + step * rate) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 4 * step) denominatorPositive).mpr
    have denominatorUpper : 1 + step * rate ≤ 2 * step * rate := by nlinarith
    have first := mul_le_mul_of_nonneg_left denominatorUpper windowPositive.le
    have second := mul_le_mul_of_nonneg_left floorLower (by positivity : 0 ≤ 4 * step)
    nlinarith
  calc
    (step * rate / (1 + step * rate)) ^ ⌊window * rate⌋₊ ≤
        (Real.exp (-(1 + step * rate)⁻¹)) ^ ⌊window * rate⌋₊ := by gcongr
    _ = Real.exp ((⌊window * rate⌋₊ : ℝ) * (-(1 + step * rate)⁻¹)) :=
      (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (-window / (4 * step)) := by
      apply Real.exp_le_exp.mpr
      calc
        (⌊window * rate⌋₊ : ℝ) * (-(1 + step * rate)⁻¹) =
            -((⌊window * rate⌋₊ : ℝ) / (1 + step * rate)) := by ring
        _ ≤ -(window / (4 * step)) := neg_le_neg quotientLower
        _ = -window / (4 * step) := by ring

end IGS.Sec31

#print axioms IGS.Sec31.geometric_resolvent_floor_clock_tail
