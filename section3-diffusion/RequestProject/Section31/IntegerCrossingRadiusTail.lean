import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-! Convert a genuine integer crossing tail into an arbitrary-radius
exponential envelope. This numerical/probability helper does not assume an
optimized exit estimate. The actual-rule consumer supplies its crossing tail. -/

namespace IGS.Sec31
open MeasureTheory
noncomputable section

theorem radius_tail_le_crossing_exponential
    {Sample State : Type*} [MeasurableSpace Sample] [PseudoMetricSpace State]
    (law : Measure Sample) [IsProbabilityMeasure law]
    (observation : Sample → ℕ → State) (center : State) (horizon : ℕ)
    (radius spatialScale time timeScale decay : ℝ)
    (radiusPositive : 0 < radius) (spatialScalePositive : 0 < spatialScale)
    (timeNonnegative : 0 ≤ time) (timeScalePositive : 0 < timeScale)
    (decayPositive : 0 < decay) (decayLessThanOne : decay < 1)
    (crossingTail : ∀ count : ℕ,
      law.real {sample | ∃ index, index ≤ horizon ∧
        (count + 2 : ℝ) * spatialScale < dist (observation sample index) center} ≤
          Real.exp (time / timeScale) * decay ^ count) :
    law.real {sample | ∃ index, index ≤ horizon ∧
      radius ≤ dist (observation sample index) center} ≤
      Real.exp (2 * (-Real.log decay) + time / timeScale +
        Real.log decay * (radius / (4 * spatialScale))) := by
  have logarithmNegative : Real.log decay < 0 := Real.log_neg decayPositive decayLessThanOne
  have ratioNonnegative : 0 ≤ radius / (4 * spatialScale) := by positivity
  by_cases large : 2 ≤ radius / (4 * spatialScale)
  · let count : ℕ := Nat.floor (radius / (4 * spatialScale))
    have countUpper : (count : ℝ) ≤ radius / (4 * spatialScale) := Nat.floor_le ratioNonnegative
    have countLower : radius / (4 * spatialScale) < (count : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have thresholdUpper : (count + 2 : ℝ) * spatialScale ≤ radius / 2 := by
      have scaled := mul_le_mul_of_nonneg_right
        (show (count + 2 : ℝ) ≤ 2 * (radius / (4 * spatialScale)) by linarith)
        spatialScalePositive.le
      have cancellation : 2 * (radius / (4 * spatialScale)) * spatialScale = radius / 2 := by
        field_simp [spatialScalePositive.ne']
        <;> ring
      simpa only [cancellation] using scaled
    have inclusion : {sample | ∃ index, index ≤ horizon ∧
        radius ≤ dist (observation sample index) center} ⊆
      {sample | ∃ index, index ≤ horizon ∧
        (count + 2 : ℝ) * spatialScale < dist (observation sample index) center} := by
      rintro sample ⟨index, bounded, displaced⟩
      exact ⟨index, bounded, (thresholdUpper.trans_lt (by linarith)).trans_le displaced⟩
    have powerExpression : decay ^ count = Real.exp ((count : ℝ) * Real.log decay) := by
      rw [Real.exp_nat_mul, Real.exp_log decayPositive]
    calc
      _ ≤ law.real {sample | ∃ index, index ≤ horizon ∧
          (count + 2 : ℝ) * spatialScale < dist (observation sample index) center} :=
        measureReal_mono inclusion
      _ ≤ Real.exp (time / timeScale) * decay ^ count := crossingTail count
      _ ≤ _ := by
        rw [powerExpression, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have reversed := mul_lt_mul_of_neg_left countLower logarithmNegative
        nlinarith
  · have probabilityBound : law.real {sample | ∃ index, index ≤ horizon ∧
        radius ≤ dist (observation sample index) center} ≤ 1 := measureReal_le_one
    apply probabilityBound.trans
    apply Real.one_le_exp_iff.mpr
    have timeBound := div_nonneg timeNonnegative timeScalePositive.le
    have reversed := mul_le_mul_of_nonpos_left (le_of_not_ge large) logarithmNegative.le
    nlinarith

end
end IGS.Sec31

#print axioms IGS.Sec31.radius_tail_le_crossing_exponential
