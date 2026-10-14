import RequestProject.Section31.ExponentialHoldingClockShift

namespace IGS.Sec31.PoissonClock
open MeasureTheory ProbabilityTheory Filter
noncomputable section

theorem holdingJumpIndex_at_arrival_shift
    (holdingTimes : ℕ → ℝ) (offset : ℕ)
    (nonnegative : ∀ index, 0 ≤ holdingTimes index)
    (tailNonexplosion : Tendsto
      (cumulativeHoldingTime (shiftedHoldingTimes offset holdingTimes)) atTop atTop)
    (time : ℝ) (timeNonnegative : 0 ≤ time) :
    holdingJumpIndex holdingTimes (cumulativeHoldingTime holdingTimes offset + time) =
      offset + holdingJumpIndex (shiftedHoldingTimes offset holdingTimes) time := by
  have interval := holdingJumpIndex_interval (shiftedHoldingTimes offset holdingTimes)
    (fun index => nonnegative (offset + index)) tailNonexplosion time timeNonnegative
  apply holdingJumpIndex_eq_of_interval holdingTimes nonnegative
    (cumulativeHoldingTime holdingTimes offset + time)
    (offset + holdingJumpIndex (shiftedHoldingTimes offset holdingTimes) time)
  · rw [← cumulativeHoldingTime_shift_add]
    linarith only [interval.1]
  · rw [Nat.add_assoc, ← cumulativeHoldingTime_shift_add]
    linarith only [interval.2]

/-- The deterministic arrival-shift identity holds almost surely for the
actual infinite iid sample, at every nonnegative elapsed time. -/
theorem holdingJumpIndex_at_arrival_shift_ae (offset : ℕ) :
    ∀ᵐ holdingTimes ∂exponentialHoldingTimeLaw, ∀ time : ℝ, 0 ≤ time →
      holdingJumpIndex holdingTimes (cumulativeHoldingTime holdingTimes offset + time) =
        offset + holdingJumpIndex (shiftedHoldingTimes offset holdingTimes) time := by
  have mappedNonexplosion :
      ∀ᵐ tail ∂exponentialHoldingTimeLaw.map (shiftedHoldingTimes offset),
        Tendsto (cumulativeHoldingTime tail) atTop atTop := by
    rw [(shiftedHoldingTimes_hasLaw offset).map_eq]
    exact exponentialHoldingTimeLaw_nonexplosion
  have tailNonexplosion := ae_of_ae_map
    (shiftedHoldingTimes_measurable offset).aemeasurable mappedNonexplosion
  filter_upwards [exponentialHoldingTimeLaw_positive, tailNonexplosion]
    with holdingTimes positive divergent
  intro time timeNonnegative
  exact holdingJumpIndex_at_arrival_shift holdingTimes offset
    (fun index => (positive index).le) divergent time timeNonnegative

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.holdingJumpIndex_at_arrival_shift
#print axioms IGS.Sec31.PoissonClock.holdingJumpIndex_at_arrival_shift_ae
