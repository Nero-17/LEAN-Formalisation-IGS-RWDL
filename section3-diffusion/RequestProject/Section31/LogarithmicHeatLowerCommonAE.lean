import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! A single full-measure set on which every positive logarithmic epsilon
is available. A countable cofinal epsilon sequence and the clipped small-time
interval make the quantifier strengthening explicit. Candidate source:
no compilation is claimed. -/

namespace IGS.Sec31
open MeasureTheory Filter
open scoped NNReal
noncomputable section

theorem logarithmic_heat_lower_common_ae
    {Point : Type*} [MeasurableSpace Point] (law : Measure Point)
    (kernel : {time : ℝ≥0 // 0 < time} → Point → ℝ) (exponent baseLogExponent : ℝ)
    (lowerFamily : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᵐ point ∂law, ∃ lowerConstant : ℝ, 0 < lowerConstant ∧
      ∃ timeThreshold : ℝ, 0 < timeThreshold ∧
      ∀ time : {time : ℝ≥0 // 0 < time}, (time.val : ℝ) ≤ timeThreshold →
      lowerConstant * (time.val : ℝ) ^ (-exponent) *
        |Real.log (time.val : ℝ)| ^ (-(baseLogExponent + epsilon)) ≤ kernel time point) :
    ∀ᵐ point ∂law, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ lowerConstant : ℝ, 0 < lowerConstant ∧ ∃ timeThreshold : ℝ, 0 < timeThreshold ∧
      ∀ time : {time : ℝ≥0 // 0 < time}, (time.val : ℝ) ≤ timeThreshold →
      lowerConstant * (time.val : ℝ) ^ (-exponent) *
        |Real.log (time.val : ℝ)| ^ (-(baseLogExponent + epsilon)) ≤ kernel time point := by
  have countableFamily : ∀ index : ℕ,
      ∀ᵐ point ∂law, ∃ lowerConstant : ℝ, 0 < lowerConstant ∧
      ∃ timeThreshold : ℝ, 0 < timeThreshold ∧
      ∀ time : {time : ℝ≥0 // 0 < time}, (time.val : ℝ) ≤ timeThreshold →
      lowerConstant * (time.val : ℝ) ^ (-exponent) *
        |Real.log (time.val : ℝ)| ^ (-(baseLogExponent + 1 / ((index : ℝ) + 1))) ≤ kernel time point := by
    intro index
    exact lowerFamily _ (by positivity)
  filter_upwards [ae_all_iff.mpr countableFamily] with point allEpsilon
  intro epsilon epsilonPositive
  obtain ⟨index, epsilonBound⟩ := exists_nat_one_div_lt epsilonPositive
  obtain ⟨lowerConstant, lowerPositive, timeThreshold, thresholdPositive, bound⟩ := allEpsilon index
  refine ⟨lowerConstant, lowerPositive, min timeThreshold (Real.exp (-1)),
    lt_min thresholdPositive (Real.exp_pos _), ?_⟩
  intro time timeSmall
  have timePositive : 0 < (time.val : ℝ) := time.property
  have logTimeBound : Real.log (time.val : ℝ) ≤ -1 := by
    have compared := Real.log_le_log timePositive (timeSmall.trans (min_le_right _ _))
    simpa only [Real.log_exp] using compared
  have logarithmAtLeastOne : 1 ≤ |Real.log (time.val : ℝ)| := by
    rw [abs_of_nonpos (logTimeBound.trans (by norm_num))]
    linarith
  have exponentOrder : -(baseLogExponent + epsilon) ≤
      -(baseLogExponent + 1 / ((index : ℝ) + 1)) := by linarith
  have logarithmOrder := Real.rpow_le_rpow_of_exponent_le logarithmAtLeastOne exponentOrder
  have coefficientNonnegative : 0 ≤ lowerConstant * (time.val : ℝ) ^ (-exponent) :=
    mul_nonneg lowerPositive.le (Real.rpow_nonneg timePositive.le _)
  exact (mul_le_mul_of_nonneg_left logarithmOrder coefficientNonnegative).trans
    (bound time (timeSmall.trans (min_le_left _ _)))

end
end IGS.Sec31

#print axioms IGS.Sec31.logarithmic_heat_lower_common_ae
