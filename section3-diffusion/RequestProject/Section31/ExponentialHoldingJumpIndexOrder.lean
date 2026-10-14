import RequestProject.Section31.ExponentialHoldingTimePaths

namespace IGS.Sec31.PoissonClock
open Filter
noncomputable section

theorem holdingJumpIndex_ge_iff (holdingTimes : ℕ → ℝ)
    (positive : ∀ index, 0 < holdingTimes index)
    (nonexplosion : Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop)
    (time : ℝ) (timeNonnegative : 0 ≤ time) (count : ℕ) :
    count ≤ holdingJumpIndex holdingTimes time ↔ cumulativeHoldingTime holdingTimes count ≤ time := by
  have interval := holdingJumpIndex_interval holdingTimes (fun index => (positive index).le)
    nonexplosion time timeNonnegative
  constructor
  · intro bound
    exact (cumulativeHoldingTime_monotone holdingTimes (fun index => (positive index).le) bound).trans interval.1
  · intro bound
    by_contra failure
    have before : holdingJumpIndex holdingTimes time + 1 ≤ count := Nat.succ_le_of_lt (Nat.lt_of_not_ge failure)
    have cumulativeBefore := cumulativeHoldingTime_monotone holdingTimes (fun index => (positive index).le) before
    exact (not_le_of_gt interval.2) (cumulativeBefore.trans bound)

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.holdingJumpIndex_ge_iff
