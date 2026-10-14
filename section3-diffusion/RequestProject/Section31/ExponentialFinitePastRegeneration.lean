import RequestProject.Section31.ExponentialFiniteHistoryRegeneration
import RequestProject.Section31.MeasurableNatFibrePartition

namespace IGS.Sec31.PoissonClock
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3500000

theorem exponential_finite_past_regeneration
    {observations : ℕ} (time : ℝ≥0)
    (pastTimes : Fin observations → ℝ≥0) (pastCounts : Fin observations → ℕ)
    (pastBefore : ∀ index, pastTimes index ≤ time)
    (future : Set (ℕ → ℝ)) (futureMeasurable : MeasurableSet future) :
    exponentialHoldingTimeLaw {holdingTimes |
        (∀ index, holdingJumpIndex holdingTimes (pastTimes index : ℝ) = pastCounts index) ∧
          residualHoldingTimes holdingTimes (time : ℝ) ∈ future} =
      exponentialHoldingTimeLaw {holdingTimes |
          ∀ index, holdingJumpIndex holdingTimes (pastTimes index : ℝ) = pastCounts index} *
        exponentialHoldingTimeLaw future := by
  let pastEvent : Set (ℕ → ℝ) :=
    {holdingTimes | ∀ index, holdingJumpIndex holdingTimes (pastTimes index : ℝ) = pastCounts index}
  let fullEvent : Set (ℕ → ℝ) :=
    {holdingTimes | holdingTimes ∈ pastEvent ∧ residualHoldingTimes holdingTimes (time : ℝ) ∈ future}
  have pastMeasurable : MeasurableSet pastEvent := by
    convert MeasurableSet.iInter (fun index : Fin observations =>
      (measurableSet_singleton (pastCounts index)).preimage
        (holdingJumpIndex_measurable (pastTimes index : ℝ))) using 1
    ext holdingTimes
    simp only [pastEvent, mem_setOf_eq, mem_iInter, mem_preimage, mem_singleton_iff]
  have fullMeasurable : MeasurableSet fullEvent :=
    pastMeasurable.inter (futureMeasurable.preimage (residualHoldingTimes_measurable (time : ℝ)))
  change exponentialHoldingTimeLaw fullEvent = exponentialHoldingTimeLaw pastEvent *
    exponentialHoldingTimeLaw future
  rw [measure_nat_fibre_partition exponentialHoldingTimeLaw
    (fun holdingTimes => holdingJumpIndex holdingTimes (time : ℝ))
    (holdingJumpIndex_measurable (time : ℝ)) fullEvent fullMeasurable]
  calc
    (∑' count : ℕ, exponentialHoldingTimeLaw
        {holdingTimes | holdingTimes ∈ fullEvent ∧ holdingJumpIndex holdingTimes (time : ℝ) = count}) =
      ∑' count : ℕ, exponentialHoldingTimeLaw
        {holdingTimes | holdingTimes ∈ pastEvent ∧ holdingJumpIndex holdingTimes (time : ℝ) = count} *
          exponentialHoldingTimeLaw future := by
      apply tsum_congr
      intro count
      have eventEquality :
          {holdingTimes : ℕ → ℝ | holdingTimes ∈ fullEvent ∧ holdingJumpIndex holdingTimes (time : ℝ) = count} =
          {holdingTimes | (∀ index, holdingJumpIndex holdingTimes (pastTimes index : ℝ) = pastCounts index) ∧
            holdingJumpIndex holdingTimes (time : ℝ) = count ∧
              residualHoldingTimes holdingTimes (time : ℝ) ∈ future} := by
        ext holdingTimes
        simp only [fullEvent, pastEvent, mem_setOf_eq]
        tauto
      rw [eventEquality]
      exact exponential_finite_history_count_regeneration time count pastTimes pastCounts
        pastBefore future futureMeasurable
    _ = (∑' count : ℕ, exponentialHoldingTimeLaw
        {holdingTimes | holdingTimes ∈ pastEvent ∧ holdingJumpIndex holdingTimes (time : ℝ) = count}) *
          exponentialHoldingTimeLaw future := by
      rw [ENNReal.tsum_mul_right]
    _ = exponentialHoldingTimeLaw pastEvent * exponentialHoldingTimeLaw future := by
      rw [← measure_nat_fibre_partition exponentialHoldingTimeLaw
        (fun holdingTimes => holdingJumpIndex holdingTimes (time : ℝ))
        (holdingJumpIndex_measurable (time : ℝ)) pastEvent pastMeasurable]

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.exponential_finite_past_regeneration
