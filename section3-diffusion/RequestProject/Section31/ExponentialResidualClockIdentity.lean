import RequestProject.Section31.ExponentialHoldingHeadTailLaw
import Mathlib.Order.Filter.AtTopBot.Group

namespace IGS.Sec31.PoissonClock
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000

theorem cumulativeHoldingTime_prepend
    (first : ℝ) (tail : ℕ → ℝ) (count : ℕ) :
    cumulativeHoldingTime (prependHoldingTime first tail) (count + 1) =
      first + cumulativeHoldingTime tail count := by
  simp only [cumulativeHoldingTime, Finset.sum_range_succ', prependHoldingTime, add_comm]

def residualHoldingTimes (holdingTimes : ℕ → ℝ) (time : ℝ) : ℕ → ℝ :=
  prependHoldingTime
    (cumulativeHoldingTime holdingTimes (holdingJumpIndex holdingTimes time + 1) - time)
    (shiftedHoldingTimes (holdingJumpIndex holdingTimes time + 1) holdingTimes)

theorem residualHoldingTimes_cumulative_succ
    (holdingTimes : ℕ → ℝ) (time : ℝ) (count : ℕ) :
    cumulativeHoldingTime (residualHoldingTimes holdingTimes time) (count + 1) =
      cumulativeHoldingTime holdingTimes (holdingJumpIndex holdingTimes time + count + 1) - time := by
  rw [residualHoldingTimes, cumulativeHoldingTime_prepend]
  have shift := cumulativeHoldingTime_shift_add holdingTimes
    (holdingJumpIndex holdingTimes time + 1) count
  rw [show holdingJumpIndex holdingTimes time + 1 + count =
    holdingJumpIndex holdingTimes time + count + 1 by omega] at shift
  linarith only [shift]

theorem residualHoldingTimes_nonexplosion
    (holdingTimes : ℕ → ℝ) (time : ℝ) (timeNonnegative : 0 ≤ time)
    (nonnegative : ∀ index, 0 ≤ holdingTimes index)
    (nonexplosion : Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop) :
    Tendsto (cumulativeHoldingTime (residualHoldingTimes holdingTimes time)) atTop atTop := by
  apply tendsto_atTop_mono _ (tendsto_atTop_add_const_right atTop (-time) nonexplosion)
  intro count
  cases count with
  | zero => simpa only [cumulativeHoldingTime, Finset.sum_range_zero, zero_add] using neg_nonpos.mpr timeNonnegative
  | succ count =>
      rw [residualHoldingTimes_cumulative_succ]
      have monotone := cumulativeHoldingTime_monotone holdingTimes nonnegative
        (show count + 1 ≤ holdingJumpIndex holdingTimes time + count + 1 by omega)
      linarith only [monotone]

theorem residualHoldingTimes_positive
    (holdingTimes : ℕ → ℝ) (time : ℝ) (timeNonnegative : 0 ≤ time)
    (positive : ∀ index, 0 < holdingTimes index)
    (nonexplosion : Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop) :
    ∀ index, 0 < residualHoldingTimes holdingTimes time index := by
  intro index
  cases index with
  | zero =>
      have interval := holdingJumpIndex_interval holdingTimes
        (fun index => (positive index).le) nonexplosion time timeNonnegative
      exact sub_pos.mpr interval.2
  | succ index => exact positive (holdingJumpIndex holdingTimes time + 1 + index)

theorem holdingJumpIndex_residual_add
    (holdingTimes : ℕ → ℝ) (time futureTime : ℝ)
    (timeNonnegative : 0 ≤ time) (futureNonnegative : 0 ≤ futureTime)
    (positive : ∀ index, 0 < holdingTimes index)
    (nonexplosion : Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop) :
    holdingJumpIndex holdingTimes (time + futureTime) =
      holdingJumpIndex holdingTimes time +
        holdingJumpIndex (residualHoldingTimes holdingTimes time) futureTime := by
  have originalInterval := holdingJumpIndex_interval holdingTimes
    (fun index => (positive index).le) nonexplosion time timeNonnegative
  have residualInterval := holdingJumpIndex_interval (residualHoldingTimes holdingTimes time)
    (fun index => (residualHoldingTimes_positive holdingTimes time timeNonnegative positive nonexplosion index).le)
    (residualHoldingTimes_nonexplosion holdingTimes time timeNonnegative
      (fun index => (positive index).le) nonexplosion) futureTime futureNonnegative
  apply holdingJumpIndex_eq_of_interval holdingTimes (fun index => (positive index).le)
    (time + futureTime) _
  · generalize countEquality : holdingJumpIndex (residualHoldingTimes holdingTimes time) futureTime = count at *
    cases count with
    | zero => simpa only [Nat.add_zero] using originalInterval.1.trans (le_add_of_nonneg_right futureNonnegative)
    | succ count =>
        rw [residualHoldingTimes_cumulative_succ] at residualInterval
        have lower := residualInterval.1
        have ordering : cumulativeHoldingTime holdingTimes
            (holdingJumpIndex holdingTimes time + count + 1) ≤ time + futureTime := by
          linarith only [lower]
        simpa only [Nat.add_assoc] using ordering
  · rw [residualHoldingTimes_cumulative_succ] at residualInterval
    linarith only [residualInterval.2]

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.cumulativeHoldingTime_prepend
#print axioms IGS.Sec31.PoissonClock.residualHoldingTimes_cumulative_succ
#print axioms IGS.Sec31.PoissonClock.residualHoldingTimes_nonexplosion
#print axioms IGS.Sec31.PoissonClock.residualHoldingTimes_positive
#print axioms IGS.Sec31.PoissonClock.holdingJumpIndex_residual_add
