import RequestProject.Section31.ExponentialHoldingTimePaths
import Mathlib.Probability.Distributions.Poisson

/-! The actual unit-exponential renewal count's zero-jump probability. -/

namespace IGS.Sec31.PoissonClock
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped ENNReal NNReal Classical
noncomputable section

 theorem unit_exponential_tail_probability (time : ℝ) (timeNonnegative : 0 ≤ time) :
    expMeasure 1 (Set.Ioi time) = ENNReal.ofReal (Real.exp (-time)) := by
  have realTail : (expMeasure 1).real (Set.Ioi time) = Real.exp (-time) := by
    rw [← Set.compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ,
      ← cdf_eq_real, cdf_expMeasure_eq zero_lt_one, if_pos timeNonnegative]
    norm_num
  calc
    expMeasure 1 (Set.Ioi time) = ENNReal.ofReal ((expMeasure 1).real (Set.Ioi time)) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ = _ := by rw [realTail]

 theorem exponentialHoldingJumpIndex_zero_probability (time : ℝ) (timeNonnegative : 0 ≤ time) :
    exponentialHoldingTimeLaw {holdingTimes | holdingJumpIndex holdingTimes time = 0} =
      ENNReal.ofReal (Real.exp (-time)) := by
  have eventEquality :
      exponentialHoldingTimeLaw {holdingTimes | holdingJumpIndex holdingTimes time = 0} =
      exponentialHoldingTimeLaw {holdingTimes : ℕ → ℝ | time < holdingTimes 0} := by
    apply measure_congr
    filter_upwards [exponentialHoldingTimeLaw_positive, exponentialHoldingTimeLaw_nonexplosion]
      with holdingTimes positive nonexplosion
    apply propext
    constructor
    · intro countZero
      have interval := holdingJumpIndex_interval holdingTimes (fun index => (positive index).le)
        nonexplosion time timeNonnegative
      simpa only [countZero, zero_add, cumulativeHoldingTime, Finset.sum_range_one] using interval.2
    · intro firstJumpLater
      apply holdingJumpIndex_eq_of_interval holdingTimes (fun index => (positive index).le) time 0
      · simpa only [cumulativeHoldingTime, Finset.range_zero, Finset.sum_empty] using timeNonnegative
      · simpa only [zero_add, cumulativeHoldingTime, Finset.sum_range_one] using firstJumpLater
  rw [eventEquality]
  have mappedEvent : exponentialHoldingTimeLaw {holdingTimes : ℕ → ℝ | time < holdingTimes 0} =
      expMeasure 1 (Set.Ioi time) := by
    rw [← exponentialHoldingTimeLaw_eval 0,
      Measure.map_apply (measurable_pi_apply 0) measurableSet_Ioi]
    rfl
  rw [mappedEvent, unit_exponential_tail_probability time timeNonnegative]

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.unit_exponential_tail_probability
#print axioms IGS.Sec31.PoissonClock.exponentialHoldingJumpIndex_zero_probability
